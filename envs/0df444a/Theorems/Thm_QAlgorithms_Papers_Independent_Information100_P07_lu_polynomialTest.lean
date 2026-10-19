-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_lu_polynomialTest
-- name    : QAlgorithms.Papers.Independent.Information100.P07.lu_polynomialTest
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:44:20.655962+00:00
-- url     : https://prove2.me/theorems/05ea2160-4766-4d3f-af47-f6e77758a3e1
-- title:
--   Unnumbered: LU equivalence as unitary intertwining equations, Eq. (S44)
-- statement:
--   For two positive unnormalized two-qutrit blocks $C,D$, LU equivalence is equivalent to existence of local complex matrices $U,V$ satisfying
--   $$U^\dagger U=V^\dagger V=I,\qquad(U\otimes V)C=D(U\otimes V).$$
--   Furthermore, after using 36 real variables for the real and imaginary entries of $U,V$, these constraints are equivalent, for every assignment of those variables, to simultaneous vanishing of a finite family of real multivariate polynomials.
--
--   This is exact algebraic feasibility. It does not identify approximate residual minimization or numerical failure with a decision procedure.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 20, Unnumbered: LU equivalence as unitary intertwining equations, Eq. (S44)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF p.20, Eq.(S44): exact intertwining and finite real polynomial feasibility. -/
theorem lu_polynomialTest (C D : Joint) (hC : C.PosSemidef) (hD : D.PosSemidef) :
    (LU C D ↔ ∃ U V : Local, Intertwining C D U V) ∧
    ∃ m : ℕ, ∃ f : Fin m → MvPolynomial RealVariables ℝ, ∀ x : RealVariables → ℝ,
      (∀ i, MvPolynomial.eval x (f i) = 0) ↔ Intertwining C D (decodeMatrix x 0) (decodeMatrix x 1) := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end
