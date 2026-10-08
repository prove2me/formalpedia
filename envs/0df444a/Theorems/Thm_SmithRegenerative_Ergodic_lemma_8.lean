-- Prove2me | Theorems.Thm_SmithRegenerative_Ergodic_lemma_8
-- name    : SmithRegenerative.Ergodic.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:08.597998+00:00
-- url     : https://prove2.me/theorems/0d04250c-f4a6-46d5-ad4a-dc03b7330556
-- title:
--   Lemma 8 — (w_{t+Z_t} − w_t)/t^{1/p} → 0 with probability one when t₀ = 0, μ₁ < ∞, κ̃_p < ∞
-- statement:
--   Let $t_1, t_2, \dots$ be a renewal process with $t_0 = 0$ and $\mu_1 = E t_1 < \infty$, and let $w_t$ be a cumulative process relative to it (conditions (C1), (C2), with identically distributed cycle variations $\tilde y_n$). Let $Z_t = \sum_{i=1}^{n_t+1} t_i - t$, so that $t + Z_t$ is a regeneration epoch after $t$. If $p > 0$ and $\tilde\kappa_p = E \tilde y_1^{\,p} < \infty$, then, with probability one,
--   $$\lim_{t \to \infty} \frac{w_{t+Z_t} - w_t}{t^{1/p}} = 0 .$$
--
--   The lemma says that the gap between the cumulative process at time $t$ and at the next completed regeneration epoch is negligible. With $p = 1$ it reduces Theorem 7 to the behaviour of $w$ along regeneration epochs.
--
--   **Formalization Note** $\tilde\kappa_p < \infty$ is integrability of $\tilde y_1^{\,p}$ (real power; $\tilde y_1 \ge 0$). The condition $w_0 = 0$ is not assumed. The limit is along real $t \to \infty$.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, pp. 26–27, §5·3, Lemma 8

import Mathlib
import Definitions.Def_SmithRegenerative_Ergodic_Renewal
import Definitions.Def_SmithRegenerative_Ergodic_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.Ergodic

/-- **Lemma 8** (Smith, *Regenerative stochastic processes*, Proc. R. Soc. Lond. A
232(1188):6–31 (1955), §5·3, p. 26): "If t₀ = 0, μ₁ < ∞, and κ̃_p < ∞ (p > 0), then
lim_{t=∞} (w_{t+Z_t} − w_t)/t^{1/p} = 0, with probability one."

Here `w_t` is a cumulative process (the standing context of §5·3), `Z_t = Σ_{i=1}^{n_t+1} t_i − t`
(p. 26) and `κ̃_p = E ỹ_1^p`, `ỹ_n` the variation of `w` over the `n`-th cycle.

Formalization Note: `μ₁ < ∞` is integrability of `t₁`; `κ̃_p < ∞` is integrability of `ỹ_1^p`
(real power; `ỹ_1 ≥ 0` at every sample point under the hypotheses). `w₀ = 0` is not assumed (the
lemma does not state it). The cumulative-process hypothesis is `IsCumulativeProcess`: (C1) read
literally, (C2), and `ỹ_n` identically distributed; no joint independence of cycle lengths and
increments. `t^{1/p}` is `Real.rpow`; the limit is along real `t → ∞`. The page's proof bound
(5·3·1) by `ỹ_{n_t+1}` alone omits the cycle `n_t`; the statement itself is unaffected. -/
theorem lemma_8 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hren : IsRenewalProcess P t)
    (ht0 : ∀ ω, t 0 ω = 0) (hμ : Integrable (t 1) P) (hcum : IsCumulativeProcess P t w)
    (p : ℝ) (hp : 0 < p) (hκ : Integrable (fun ω => cycleVariation t w 1 ω ^ p) P) :
    ∀ᵐ ω ∂P, Tendsto (fun s : ℝ => (w (s + Z t s ω) ω - w s ω) / s ^ (1 / p)) atTop
      (𝓝 0) := by sorry

end SmithRegenerative.Ergodic
