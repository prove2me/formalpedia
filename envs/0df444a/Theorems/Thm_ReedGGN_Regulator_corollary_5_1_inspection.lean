-- Prove2me | Theorems.Thm_ReedGGN_Regulator_corollary_5_1_inspection
-- name    : ReedGGN.Regulator.corollary_5_1_inspection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:27.570354+00:00
-- url     : https://prove2.me/theorems/302e1091-7737-4956-bd59-1bfa29a218cd
-- title:
--   Proof of Corollary 5.1 — with F₀ = F_e, Q̄₀ = 1 and Ā = e the fluid equation reduces to Q̄(t) = 1 + ∫₀ᵗ (Q̄(t−s)−1)⁺ dF(s), whose unique solution is Q̄ ≡ 1
-- statement:
--   Let $\mu$ be the law of a service time: a probability measure on $[0,\infty)$ with finite mean $\int s\,\mu(ds)=1$. Let $F$, $G=1-F$ and $F_e$ be its distribution function, tail and equilibrium distribution (5.4), and $\bar F_e=1-F_e$. Take $F_0=F_e$, $\bar Q_0=1$ and $\bar A=e$, so that (4.7) reads
--   $$\bar Q(t)=\min(1,1)\bar F_e(t)+(1-1)^+G(t)+\int_0^tG(t-s)\,ds+\int_{[0,t]}(\bar Q(t-s)-1)^+\,dF(s),\qquad t\ge0.$$
--   Then:
--
--   1. $\min(1,1)\bar F_e(t)+(1-1)^+G(t)+\int_0^tG(t-s)\,ds=1$ for every $t\ge0$, so the equation is $\bar Q(t)=1+\int_{[0,t]}(\bar Q(t-s)-1)^+\,dF(s)$;
--   2. $\bar Q\equiv1$ solves it;
--   3. every càdlàg solution equals $1$ on $[0,\infty)$.
--
--   This is the deterministic step of the proof of Corollary 5.1: under equilibrium initial conditions the fluid limit is constant.
--
--   **Formalization Note** The paper calls Corollary 5.1 "a corollary to Theorem 5.1 of Section 4", meaning Theorem 4.1. The weak-convergence part of the corollary is not stated. Uniqueness (item 3) uses that $\mu(\{0\})<1$, which follows from mean $1$ and support in $[0,\infty)$.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 18, proof of Corollary 5.1; Eq. (5.4)

import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation
import Definitions.Def_ReedGGN_Regulator_FluidInput

namespace ReedGGN.Regulator

open MeasureTheory

/-- Proof of Corollary 5.1 (p. 18): for a service law `μ` (support in `[0, ∞)`, mean `1`),
with `F_0 = F_e`, `Q̄₀ = 1` and `Ā = e`, the input of (4.7) equals `1` for `t ≥ 0`, and
`Q̄ ≡ 1` is the unique càdlàg solution of
`Q̄(t) = 1 + ∫_0^t (Q̄(t − s) − 1)^+ dF(s)` on `[0, ∞)`. -/
theorem corollary_5_1_inspection (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ_nonneg : μ (Set.Iio 0) = 0) (hμ_int : Integrable id μ)
    (hμ_mean : ∫ s, s ∂μ = 1) :
    (∀ t, 0 ≤ t → fluidInput 1 (fun r => 1 - Fe μ r) μ t = 1) ∧
    SolvesRegulator μ (-1) (fluidInput 1 (fun r => 1 - Fe μ r) μ) (fun _ => 1) ∧
    (∀ Q : ℝ → ℝ, IsCadlag Q →
      SolvesRegulator μ (-1) (fluidInput 1 (fun r => 1 - Fe μ r) μ) Q →
      Set.EqOn Q (fun _ => 1) (Set.Ici 0)) := by sorry

end ReedGGN.Regulator
