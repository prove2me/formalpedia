-- Prove2me | Theorems.Thm_PersuadeFly_lemma_3
-- name    : PersuadeFly.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:31:49.830903+00:00
-- url     : https://prove2.me/theorems/ccbcadd8-509e-4c1b-be9b-6932da2b1cdb
-- title:
--   Lemma 3, p.40 — $\mathsf{OPT}(\mu_1)-\mathsf{OPT}(\mu_2)\le\mathsf{Gap}(\mu_1,\mathsf B_1(\mu_1,\|\mu_1-\mu_2\|_1))+\frac12\|\mu_1-\mu_2\|_1$
-- statement:
--   For any $\mu_1,\mu_2\in\Delta(\Omega)$,
--   $$
--   \mathsf{OPT}(\mu_1)-\mathsf{OPT}(\mu_2)\le\mathsf{Gap}\big(\mu_1,\mathsf B_1(\mu_1,\|\mu_1-\mu_2\|_1)\big)+\frac12\,\|\mu_1-\mu_2\|_1 .
--   $$
--   The benchmark can drop between two priors by at most the cost of being persuasive on a ball containing both, plus a Lipschitz term. It controls the difference between the true benchmark $\mathsf{OPT}(\mu^*)$ and the benchmark at the empirical distribution.
--
--   Differences from the source:
--   - encoding: OPT(μ) = max_σ V(μ, σ) subject to σ ∈ Pers(μ) → the supremum of V(μ, ·) over Pers(μ); reason: the maximum is attained (compact nonempty polytope), so the two values coincide; p.23 writes the sup
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Lemma 3, p.40

import Mathlib
import Definitions.Def_PersuadeFly_gap
import Definitions.Def_PersuadeFly_ball1

namespace PersuadeFly

/-- **Lemma 3.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Lemma 3, p.40: for any `μ₁, μ₂ ∈ Δ(Ω)`,
`OPT(μ₁) − OPT(μ₂) ≤ Gap(μ₁, B₁(μ₁, ‖μ₁ − μ₂‖₁)) + ½ ‖μ₁ − μ₂‖₁`. -/
theorem lemma_3 {Ω A : Type} [Fintype Ω] [Nontrivial Ω] [Fintype A] [Nontrivial A]
    (I : Instance Ω A) (μ1 μ2 : Ω → ℝ) (hμ1 : μ1 ∈ stdSimplex ℝ Ω) (hμ2 : μ2 ∈ stdSimplex ℝ Ω) :
    opt I μ1 - opt I μ2 ≤ gap I μ1 (ball1 μ1 (l1Dist μ1 μ2)) + 1 / 2 * l1Dist μ1 μ2 := by sorry

end PersuadeFly
