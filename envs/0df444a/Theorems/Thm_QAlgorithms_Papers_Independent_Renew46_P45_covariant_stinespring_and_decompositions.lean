-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P45_covariant_stinespring_and_decompositions
-- name    : QAlgorithms.Papers.Independent.Renew46.P45.covariant_stinespring_and_decompositions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:48:18.673262+00:00
-- url     : https://prove2.me/theorems/77e7f3fa-7c9c-42b8-a370-5758efef6583
-- title:
--   Covariant Stinespring dilation and finite CP decompositions
-- statement:
--   Let $G$ be any group, let $\pi_i:G\to U(H_i)$ be finite-dimensional unitary representations, and let $T:B(H_2)\to B(H_1)$ be a complex-linear completely positive map satisfying
--   $$
--   \pi_1(g)T(X)\pi_1(g)^*=T(\pi_2(g)X\pi_2(g)^*).
--   $$
--   There exist a finite-dimensional unitary representation $\widetilde\pi:G\to U(E)$ and a linear map $V:H_1\to H_2\otimes E$ such that
--   $$
--   V\pi_1(g)=(\pi_2(g)\otimes\widetilde\pi(g))V,\qquad T(X)=V^*(X\otimes I_E)V.
--   $$
--   For every finite CP decomposition $T=\sum_iT_i$ there are positive operators $F_i\in B(E)$ such that
--   $$
--   \sum_iF_i=I_E,\qquad T_i(X)=V^*(X\otimes F_i)V.
--   $$
--   If a summand $T_i$ is covariant with respect to the same representations, its effect can be chosen in this same decomposition to satisfy $F_i\widetilde\pi(g)=\widetilde\pi(g)F_i$ for every $g$. No unitality is assumed, so $V$ is not generally an isometry. A zero auxiliary carrier is permitted for zero maps.
--
--   This numbered background interface is credited by the paper to Scutaru [19], Stinespring [18], and the CP Radon–Nikodym argument.
--
--   **Source Correction** Printed clause (2) asserts commutation even for noncovariant summands; the final proof paragraph explicitly requires covariance of each summand. The statement retains arbitrary CP decompositions, and conditions commutation on summand covariance. Independent moderation of the correction remains required.
-- source:
--   Optimal Cloning of Pure States, Judging Single Clones, arXiv:quant-ph/9807010v1, PDF p. 15, Theorem 8, corrected clause (2)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Renew46.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P45.unitaryMeasurable

/-- PDF p.15 Theorem 8, corrected by its final proof paragraph: one covariant
Stinespring dilation represents every finite CP decomposition by positive
effects; commuting effects are asserted for covariant summands. No unitality,
compactness, smoothness or isometry of V is imposed. Auxiliary dimension zero
is allowed, in particular for the zero CP map. -/
theorem covariant_stinespring_and_decompositions {G : Type*} [Group G]
    (h1 h2 : ℕ) (pi1 : G →* U h1) (pi2 : G →* U h2)
    (T : Mat h2 →ₗ[ℂ] Mat h1) (hCP : QAlgorithms.Entanglement.IsCompletelyPositive T)
    (hcov : ∀ g : G, ∀ X : Mat h2,
      (pi1 g : Mat h1) * T X * (pi1 g : Mat h1)ᴴ =
        T ((pi2 g : Mat h2) * X * (pi2 g : Mat h2)ᴴ)) :
    ∃ k : ℕ, ∃ pie : G →* U k, ∃ V : Matrix (Fin h2 × Fin k) (Fin h1) ℂ,
      (∀ g : G, V * (pi1 g : Mat h1) =
        Matrix.kronecker (pi2 g : Mat h2) (pie g : Mat k) * V) ∧
      (∀ X : Mat h2, T X = Vᴴ * Matrix.kronecker X (1 : Mat k) * V) ∧
      ∀ r : ℕ, ∀ S : Fin r → (Mat h2 →ₗ[ℂ] Mat h1),
        (∀ i, QAlgorithms.Entanglement.IsCompletelyPositive (S i)) → (∑ i, S i) = T →
        ∃ F : Fin r → Mat k, (∀ i, (F i).PosSemidef) ∧ (∑ i, F i) = 1 ∧
          (∀ i X, S i X = Vᴴ * Matrix.kronecker X (F i) * V) ∧
          (∀ i, (∀ g : G, ∀ X : Mat h2,
            (pi1 g : Mat h1) * S i X * (pi1 g : Mat h1)ᴴ =
              S i ((pi2 g : Mat h2) * X * (pi2 g : Mat h2)ᴴ)) →
            ∀ g : G, F i * (pie g : Mat k) = (pie g : Mat k) * F i) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P45

end
