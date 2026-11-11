-- Prove2me | Theorems.Thm_PartialHomog_Threshold_lemma_E_13_inv_pow_linearIndependent
-- name    : PartialHomog.Threshold.lemma_E_13_inv_pow_linearIndependent
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:27:23.999123+00:00
-- url     : https://prove2.me/theorems/68b89023-6b9b-4969-9ebf-3cbdb0abd4ac
-- title:
--   Proof of Lemma E.13 — the rational functions $\lambda_G^{-p}$ of pairwise non-proportional linear forms are linearly independent
-- statement:
--   Let $\lambda_G$ ($G$ in a finite index set) be nonzero real linear forms in $z=(z_0,\dots,z_{N-1})$, pairwise non-proportional (no $\lambda_G$ is a scalar multiple of $\lambda_H$ for $G\ne H$), and let $p\ge1$. Then the rational functions
--   $$\lambda_G^{-p}\in\mathbb R(z)$$
--   are linearly independent over $\mathbb R$.
--
--   In the proof of Lemma E.13 the $\lambda_G$ represent the classes of proportional linear forms among $\ell_1,\dots,\ell_D$, and this independence separates the power sums class by class.
--
--   **Formalization Note** $\mathbb R(z)$ is `FractionRing (MvPolynomial (Fin N) ℝ)` with its $\mathbb R$-algebra structure; $\lambda_G^{-p}$ is `(algebraMap _ _ (lam G))⁻¹ ^ p`.
--
--   Differences from the source:
--   - encoding: classes G of proportional forms, a representative λ_G per class → any finite family `lam : ι → MvPolynomial (Fin N) ℝ` of nonzero, pairwise non-proportional linear forms; reason: representatives of distinct classes are exactly such a family
--   - encoding: rational functions λ_G^{-p} → elements of `FractionRing (MvPolynomial (Fin N) ℝ)`; reason: the field of rational functions
-- source:
--   Spiizer, Partial Homogenization and the Structure of Optimal Algebraic Algorithms, STOC 2027 submission (manuscript sha256 33096d05…), p. 27 (PDF 29), proof of Lemma E.13

import Mathlib
import Definitions.Def_PartialHomog_Threshold_Components

open MvPolynomial

namespace PartialHomog.Threshold

/-- Proof of Lemma E.13 (p. 27): for finitely many nonzero, pairwise non-proportional real linear
forms `λ_G` and an integer `p ≥ 1`, the rational functions `λ_G^{-p}` are linearly independent
over `ℝ` (in the field of fractions of `ℝ[z]`). -/
theorem lemma_E_13_inv_pow_linearIndependent {N : ℕ} {ι : Type*} [Fintype ι]
    (lam : ι → MvPolynomial (Fin N) ℝ) (hlin : ∀ G, IsLinearForm (lam G))
    (hne : ∀ G, lam G ≠ 0) (hnp : ∀ G H, G ≠ H → ∀ c : ℝ, lam G ≠ c • lam H)
    (p : ℕ) (hp : 1 ≤ p) :
    LinearIndependent ℝ (fun G => ((algebraMap (MvPolynomial (Fin N) ℝ)
      (FractionRing (MvPolynomial (Fin N) ℝ)) (lam G))⁻¹) ^ p) := by sorry

end PartialHomog.Threshold
