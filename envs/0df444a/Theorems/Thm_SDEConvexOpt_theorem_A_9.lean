-- Prove2me | Theorems.Thm_SDEConvexOpt_theorem_A_9
-- name    : SDEConvexOpt.theorem_A_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:25:28.72299+00:00
-- url     : https://prove2.me/theorems/f56ba436-67b8-4012-bc3b-df1e223eb677
-- title:
--   Theorem A.9 — $\xi+A_t-U_t+M_t\ge0$ with $\lim A_t<\infty$ converges a.s., and $\lim U_t<\infty$ a.s.
-- statement:
--   Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space. Let $(A_t)_{t\ge0}$ and $(U_t)_{t\ge0}$ be continuous adapted increasing processes with $A_0=U_0=0$ a.s., let $(M_t)_{t\ge0}$ be a real valued continuous local martingale with $M_0=0$ a.s., and let $\xi$ be a nonnegative $\mathcal F_0$-measurable random variable. Define
--   $$
--   X_t=\xi+A_t-U_t+M_t,\qquad t\ge0 .
--   $$
--   If $X_t$ is nonnegative and $\lim_{t\to\infty}A_t<\infty$ a.s., then almost surely $\lim_{t\to\infty}X_t$ exists and is finite, and $\lim_{t\to\infty}U_t<\infty$.
--
--   This nonnegative-semimartingale convergence theorem turns Itô's formula (3.1) into (3.2) and (3.3).
--
--   Differences from the source:
--   - encoding: "continuous", "increasing" processes → almost every path is continuous, resp. monotone; reason: the paper's definition of a continuous process, p.7
--   - encoding: continuous local martingale → `EthierKurtz.IsSourceLocalMartingale` (stopped martingales along a Mathlib localizing sequence) with a.s. continuous paths; reason: the standard definition; published vocabulary
--   - encoding: "$X_t$ is nonnegative" → for every $t$, $X_t\ge0$ a.s.; reason: with a.s. continuous paths this is the same as a.s. for all $t$
--   - encoding: $\lim_{t\to\infty}A_t<\infty$, $\lim_{t\to\infty}U_t<\infty$ → the range of the path is bounded above; reason: the paths are increasing, so the limit exists in $[0,\infty]$ and is finite iff the path is bounded
--   - encoding: time $t\ge0$ → `ℝ≥0`, Mathlib `Filtration ℝ≥0`; reason: Lean convention
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, Theorem A.9, p.35 (cited from Mao [35, Theorem 1.3.9])

import Definitions.Def_EthierKurtz_IsSourceLocalMartingale

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace SDEConvexOpt

open EthierKurtz

/-- Theorem A.9 of Maulen S., Fadili, Attouch, arXiv:2207.02750v1, p.35 (cited from
[35, Theorem 1.3.9]): let `{Aₜ}` and `{Uₜ}` be two continuous adapted increasing processes with
`A₀ = U₀ = 0` a.s., let `{Mₜ}` be a real valued continuous local martingale with `M₀ = 0` a.s., and
let `ξ` be a nonnegative `𝓕₀`-measurable random variable. Define `Xₜ = ξ + Aₜ − Uₜ + Mₜ` for
`t ≥ 0`. If `Xₜ` is nonnegative and `lim_{t→∞} Aₜ < ∞` a.s., then a.s. `lim_{t→∞} Xₜ` exists and is
finite, and `lim_{t→∞} Uₜ < ∞`.

**Formalization Note** Time is `ℝ≥0` and `𝓕` a Mathlib `Filtration ℝ≥0` (no usual conditions).
"Continuous" and "increasing" hold for almost every path (the paper's "continuous", p.7). The
local martingale is the published `EthierKurtz.IsSourceLocalMartingale` (stopped martingales
along a localizing sequence). "`Xₜ` nonnegative" is `Xₜ ≥ 0` a.s. for every `t`. Since `A` and `U` are
increasing, `lim Aₜ < ∞` and `lim Uₜ < ∞` are stated as bounded ranges. -/
theorem theorem_A_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (A U M : ℝ≥0 → Ω → ℝ) (ξ : Ω → ℝ)
    (hA : Adapted ℱ A) (hAc : ∀ᵐ ω ∂P, Continuous (fun t => A t ω))
    (hAm : ∀ᵐ ω ∂P, Monotone (fun t => A t ω)) (hA0 : ∀ᵐ ω ∂P, A 0 ω = 0)
    (hU : Adapted ℱ U) (hUc : ∀ᵐ ω ∂P, Continuous (fun t => U t ω))
    (hUm : ∀ᵐ ω ∂P, Monotone (fun t => U t ω)) (hU0 : ∀ᵐ ω ∂P, U 0 ω = 0)
    (hM : IsSourceLocalMartingale P ℱ M) (hMc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hM0 : ∀ᵐ ω ∂P, M 0 ω = 0)
    (hξ : Measurable[ℱ 0] ξ) (hξ0 : ∀ ω, 0 ≤ ξ ω)
    (hX : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, 0 ≤ ξ ω + A t ω - U t ω + M t ω)
    (hAlim : ∀ᵐ ω ∂P, BddAbove (Set.range fun t => A t ω)) :
    ∀ᵐ ω ∂P, (∃ c : ℝ, Tendsto (fun t => ξ ω + A t ω - U t ω + M t ω) atTop (𝓝 c)) ∧
      BddAbove (Set.range fun t => U t ω) := by sorry

end SDEConvexOpt
