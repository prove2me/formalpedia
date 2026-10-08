-- Prove2me | Theorems.Thm_SmithRegenerative_CLT_lemma_8
-- name    : SmithRegenerative.CLT.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:42.50138+00:00
-- url     : https://prove2.me/theorems/8dcbb456-bf70-4877-9dc7-b58a4b773b7e
-- title:
--   Lemma 8 — (w_{t+Z_t} − w_t)/t^{1/p} → 0 with probability one when μ₁ < ∞ and κ̃_p < ∞
-- statement:
--   Let $w_t$ be a cumulative process on a renewal process $t_1, t_2, \dots$ with $t_0 = 0$ and $w_0 = 0$ (see the model definition), let $n_t$ be the number of regenerations in $[0,t]$, and let
--   $$Z_t = \sum_{i=1}^{n_t+1} t_i - t.$$
--   Let $p > 0$. If $\mu_1 = E t_1 < \infty$ and $\tilde\kappa_p = E \tilde y_1^{\,p} < \infty$, where $\tilde y_1$ is the variation of $w$ over the first cycle, then with probability one
--   $$\lim_{t \to \infty} \frac{w_{t+Z_t} - w_t}{t^{1/p}} = 0.$$
--
--   The value $w_{t+Z_t}$ is a sum of whole-cycle increments, $w_{t+Z_t} = \sum_{i=1}^{n_t+1} y_i$, so the lemma says that the incomplete cycle at time $t$ is negligible on the scale $t^{1/p}$. With $p = 2$ it is the step that transfers a central limit theorem from the random sums to $w_t$ itself (Theorem 9).
--
--   **Formalization Note** The single process is the model with $M = 1$. $t^{1/p}$ and $\tilde y_1^{\,p}$ are real powers; $\tilde y_1 \ge 0$.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 26, Lemma 8

import Mathlib
import Definitions.Def_SmithRegenerative_CLT_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.CLT

/-- Smith (1955), Lemma 8, p. 26: "If `t₀ = 0`, `μ₁ < ∞`, and `κ̃_p < ∞` (`p > 0`), then
`lim_{t=∞} (w_{t+Z_t} − w_t)/t^{1/p} = 0`, with probability one."

For a cumulative process `w` (with `t₀ = 0`, `w₀ = 0`), `Z_t = Σ₁^{n_t+1} t_i − t` and
`κ̃_p = E ỹ₁^p`.

**Formalization Note** The single process is the model with `M = 1`. `t ^ (1/p)` is the real
power, positive for `t > 0`; `ỹ₁ ≥ 0` (a variation increment), so `ỹ₁ ^ p` is the real power of a
non-negative number. -/
theorem lemma_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hw : IsCumulativeModel P τ (fun _ : Fin 1 => w))
    (hμ : Integrable (τ 1) P) (p : ℝ) (hp : 0 < p)
    (hκp : Integrable (fun ω => varIncr w τ 1 ω ^ p) P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => (w (t + overshoot τ t ω) ω - w t ω) / t ^ (1 / p))
      atTop (𝓝 0) := by sorry

end SmithRegenerative.CLT
