-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P36_affine_cyclotomic_quotient
-- name    : QAlgorithms.Papers.Independent.Intake100.P36.affine_cyclotomic_quotient
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:59:38.007224+00:00
-- url     : https://prove2.me/theorems/e2559a0f-1c97-4fa5-811c-378ec1d565fe
-- title:
--   The canonical affine cyclotomic quotient
-- statement:
--   Let R be a commutative integral domain with identity, let r≥1 and n≥0, let q be a unit of R, and let Q=(Q₁,…,Qᵣ) be an indexed parameter tuple, allowing repeated and zero values. Let H be the Ariki–Koike algebra with the cyclotomic and quadratic polynomial relations equal to zero, and put Lₖ=q^(1−k)Tₖ₋₁⋯T₁T₀T₁⋯Tₖ₋₁. Assume n≥1 and every Q_s is a unit. Let Ĥ_n be the corrected extended affine Hecke algebra of §2.4. Then there is an R-algebra isomorphism
--
--   $$\widehat H_n/\langle(X_1-Q_1)\cdots(X_1-Q_r)\rangle\ \cong\ H,$$
--
--   which sends every T_i to T_i and every X_j to L_j. The quotient ideal is two-sided. The unit condition follows from PDF p.8 and is essential for the images of invertible X_j; no arbitrary isomorphism is substituted for this canonical map.
-- source:
--   The representation theory of the Ariki-Koike and cyclotomic q-Schur algebras, arXiv:math/0204025v1, PDF p. 7, affine-quotient

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P36

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P36

open QAlgorithms.Papers.Independent.Renew46.P26 (Adjacent adjacentPerm nextPosition)

open QAlgorithms.Papers.Independent.Support21.P06 (wordPerm IsReducedWord)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The affine-quotient assertion, PDF pp.7-8, corrected using p.8's unit-parameter domain.
The isomorphism is pinned by T_i↦T_i and X_j↦L_j, rather than an arbitrary algebra isomorphism. -/
theorem affine_cyclotomic_quotient {R : Type*} [CommRing R] [IsDomain R]
    {r n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n) (q : Rˣ) (Q : Fin r → R)
    (hQ : ∀ s, IsUnit (Q s)) :
    ∃ e : AffineCyclotomic q Q n ≃ₐ[R] ArikiKoike q Q n,
      (∀ i, 1 ≤ i → i < n →
        e (RingQuot.mkAlgHom R (affineCyclotomicRel q Q n) (affineT q n i)) = akT q Q n i) ∧
      (∀ j : Fin n,
        e (RingQuot.mkAlgHom R (affineCyclotomicRel q Q n) (affineHeckeX q j false)) = cyclotomicJM q Q j) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P36

end
