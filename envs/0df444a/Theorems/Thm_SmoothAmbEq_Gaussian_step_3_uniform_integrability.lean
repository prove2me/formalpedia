-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_step_3_uniform_integrability
-- name    : SmoothAmbEq.Gaussian.step_3_uniform_integrability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:37.536326+00:00
-- url     : https://prove2.me/theorems/1c3e5f45-080b-4d4d-a557-01db2e46e900
-- title:
--   Appendix G, Step 3, p. 40 — uniform integrability of (1/h)∫_t^{t+h} 𝒜^{z,π}g^z ds (Assumption 4.2)
-- statement:
--   Assume the hypotheses of Theorem 5.5. Let $\pi\in\Pi$ and $(t,x,\beta)\in[0,T)\times\mathbb R^2$. There exists $\tilde t\in(t,T)$ such that, for all $z\in\mathbb R$, the family
--   $$\Big\{\frac1h\int_t^{t+h}\mathcal A^{z,\pi}g^z(s,X^{z,\pi}_s,\beta^z_s)\,ds\Big\}_{0<h<\tilde t-t}$$
--   is uniformly integrable, where $X^{z,\pi},\beta^z$ are started at $X_t=x$, $\beta^z_t=\beta$.
--
--   This is the Gaussian instance of Assumption 4.2 of the verification theorem: it allows passing to the limit $h\to0^+$ inside the expectation of the averaged generator.
--
--   **Formalization Note** "Under the conditional probability $\mathbb P[\cdot\mid X^{z,\pi}_t=x,\beta^z_t=\beta]$" is the inside system started at $(t,x,\beta)$. $\tilde t$ is chosen before $z$. Uniform integrability is Mathlib's `UniformIntegrable` with exponent $1$ on the probability space, for every strong solution $X$.
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, p. 40, Appendix G, Step 3

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace SmoothAmbEq.Gaussian

/-- Appendix G, Step 3, p. 40. Under the hypotheses of Theorem 5.5, let `π ∈ Π` and
`(t, x, β) ∈ [0, T) × ℝ²`. There exists `t̃ ∈ (t, T)` such that for all `z ∈ ℝ` the family
`{(1/h) ∫_t^{t+h} 𝒜^{z,π} g^z(s, X^{z,π}_s, β^z_s) ds}_{0 < h < t̃ - t}` is uniformly integrable
for the wealth started at `(t, x, β)`. -/
theorem step_3_uniform_integrability (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : max a (1 - 1 / 2 * (M.σ ^ 2 / (M.σ₀ ^ 2 * M.T))) < M.α) (c : Coeffs)
    (hc : SolvesODE510 M c) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P)
    (π : Strategy) (hπ : Admissible M P W π) (t : ℝ) (ht : t ∈ Ico 0 M.T) (x β : ℝ) :
    ∃ tt ∈ Ioo t M.T, ∀ z : ℝ, ∀ X : ℝ → Ω → ℝ, IsInsideWealth M P W π z t x β X →
      UniformIntegrable
        (fun h : Ioo (0 : ℝ) (tt - t) => fun ω => (1 / (h : ℝ)) *
          ∫ s in t..t + h, gen M z (π s (X s ω) (betaZ M W z t β s ω)) (gz M c z) s (X s ω)
            (betaZ M W z t β s ω))
        1 P := by sorry

end SmoothAmbEq.Gaussian
