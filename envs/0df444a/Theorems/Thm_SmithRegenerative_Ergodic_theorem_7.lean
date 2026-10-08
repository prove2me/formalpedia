-- Prove2me | Theorems.Thm_SmithRegenerative_Ergodic_theorem_7
-- name    : SmithRegenerative.Ergodic.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:06.807247+00:00
-- url     : https://prove2.me/theorems/9fe24ab8-882c-4cae-9368-e94c7603f786
-- title:
--   Theorem 7 (the ergodic theorem) — a cumulative process satisfies w_t/t → κ₁/μ₁ with probability one
-- statement:
--   Let $t_1, t_2, \dots$ be a renewal process (independent, identically distributed, non-negative, $P\{t_1 = 0\} < 1$) with delay $t_0 = 0$ and regeneration epochs $T_k = t_1 + \dots + t_k$. Let $w_t$ be a cumulative process relative to it:
--
--   1. (C1) the cycle increments $y_n = w_{T_n} - w_{T_{n-1}}$, $n \ge 1$, are independent and identically distributed;
--   2. (C2) with probability one, $w$ is of bounded variation on every finite interval;
--   3. the cycle variations $\tilde y_n$ (the total variation of $w$ over $[T_{n-1}, T_n]$) are identically distributed.
--
--   Suppose $\mu_1 = E t_1 < \infty$, $\tilde\kappa_1 = E \tilde y_1 < \infty$, and $w_0 = 0$. Then, with $\kappa_1 = E y_1$,
--   $$\lim_{t \to \infty} \frac{w_t}{t} = \frac{\kappa_1}{\mu_1} \quad \text{with probability one.}$$
--
--   This is the ergodic theorem for regenerative processes: the long-run average rate of a quantity accumulated over a regenerative system equals the expected accumulation per cycle divided by the expected cycle length (the renewal–reward theorem in later terminology).
--
--   **Formalization Note** (C1) is read literally; no independence between cycle lengths and increments is assumed. $\mu_1 < \infty$ and $\tilde\kappa_1 < \infty$ are integrability hypotheses; $\mu_1 > 0$ is a consequence of $P\{t_1 = 0\} < 1$ and is not assumed separately; $\kappa_1$ is finite because $|y_1| \le \tilde y_1$. The conditions $t_0 = 0$ and $w_0 = 0$ hold at every sample point. The limit is along real $t \to \infty$.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 27, §5·3, Theorem 7

import Mathlib
import Definitions.Def_SmithRegenerative_Ergodic_Renewal
import Definitions.Def_SmithRegenerative_Ergodic_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.Ergodic

/-- **Theorem 7 (the ergodic theorem)** (Smith, *Regenerative stochastic processes*, Proc. R.
Soc. Lond. A 232(1188):6–31 (1955), §5·3, p. 27): "If w_t is a cumulative process (satisfying
(C1) and (C2)); and if μ₁ < ∞ and κ̃₁ < ∞; and if t₀ = 0 and we define w₀ = 0, then
lim_{t=∞} w_t/t = κ₁/μ₁ with probability one."

Formalization Note: `t` is the general renewal process `t₀, t₁, …` (`IsRenewalProcess`: `t₁, t₂,
…` i.i.d., non-negative, `P{t₁ = 0} < 1`) with `t₀ = 0` at every sample point; `w` is a real
process with `w₀ = 0` at every sample point. `IsCumulativeProcess` is (C1) read literally (the
cycle increments `y_n = w_{T_n} − w_{T_{n−1}}` i.i.d.), (C2) (almost every path of bounded
variation on every `[0, s]`), and the cycle variations `ỹ_n` identically distributed (the
paper's notation `κ̃_r` presupposes it); no joint independence of cycle lengths and increments
is assumed. `μ₁ < ∞` is integrability of `t₁`, `κ̃₁ < ∞` integrability of `ỹ₁`;
`μ₁ = ∫ t₁ dP` is strictly positive under the hypotheses and is not assumed positive separately;
`κ₁ = ∫ y₁ dP` (`y₁` is integrable since `|y₁| ≤ ỹ₁` almost surely). The limit is along real
`t → ∞`. -/
theorem theorem_7 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hren : IsRenewalProcess P t)
    (ht0 : ∀ ω, t 0 ω = 0) (hw0 : ∀ ω, w 0 ω = 0) (hμ : Integrable (t 1) P)
    (hcum : IsCumulativeProcess P t w) (hκ : Integrable (cycleVariation t w 1) P) :
    ∀ᵐ ω ∂P, Tendsto (fun s : ℝ => w s ω / s) atTop
      (𝓝 ((∫ ω, cycleIncrement t w 1 ω ∂P) / ∫ ω, t 1 ω ∂P)) := by sorry

end SmithRegenerative.Ergodic
