-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P36_jm_commuting_and_symmetric_central
-- name    : QAlgorithms.Papers.Independent.Intake100.P36.jm_commuting_and_symmetric_central
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:58:57.64248+00:00
-- url     : https://prove2.me/theorems/204e11b5-b3ba-4f9b-9a7e-2e58c1643939
-- title:
--   Commuting JM elements and central symmetric polynomials
-- statement:
--   Let R be a commutative integral domain with identity, let r≥1 and n≥0, let q be a unit of R, and let Q=(Q₁,…,Qᵣ) be an indexed parameter tuple, allowing repeated and zero values. Let H be the Ariki–Koike algebra with the cyclotomic and quadratic polynomial relations equal to zero, and put Lₖ=q^(1−k)Tₖ₋₁⋯T₁T₀T₁⋯Tₖ₋₁. The JM elements commute pairwise, and every symmetric polynomial in them is central:
--
--   $$L_iL_j=L_jL_i,\qquad R[L_1,\ldots,L_n]^{S_n}\subseteq Z(H).$$
--
--   The first assertion also says that the subalgebra they generate is abelian. This inclusion holds without parameter separation or semisimplicity.
-- source:
--   The representation theory of the Ariki-Koike and cyclotomic q-Schur algebras, arXiv:math/0204025v1, PDF p. 4, JM-commutativity

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P36

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P36

open QAlgorithms.Papers.Independent.Renew46.P26 (Adjacent adjacentPerm nextPosition)

open QAlgorithms.Papers.Independent.Support21.P06 (wordPerm IsReducedWord)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Unnumbered JM-commutativity and central inclusion, PDF p.4, for every parameter tuple.
No separation, nonzero-Q, field, or semisimplicity hypothesis is used. -/
theorem jm_commuting_and_symmetric_central {R : Type*} [CommRing R] [IsDomain R]
    {r n : ℕ} (hr : 1 ≤ r) (q : Rˣ) (Q : Fin r → R) :
    (∀ i j : Fin n, Commute (cyclotomicJM q Q i) (cyclotomicJM q Q j)) ∧
      ∀ p : MvPolynomial (Fin n) R, p.IsSymmetric →
        jmEval q Q p ∈ Subalgebra.center R (ArikiKoike q Q n) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P36

end
