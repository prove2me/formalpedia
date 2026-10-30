-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_schur_excess_height_zero
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.schur_excess_height_zero
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:47:33.980512+00:00
-- url     : https://prove2.me/theorems/6be06c46-aa89-4f07-9420-8230eb10da4b
-- title:
--   Proposition 2.12
-- statement:
--   If a partition $\lambda$ has more than $d$ nonzero rows, then its Schur polynomial in $d$ variables is identically zero:
--
--   $$\ell(\lambda)>d\ \Longrightarrow\ s_\lambda(x_1,\ldots,x_d)\equiv0.$$
--
--   The polynomial is defined for unrestricted shapes by zero extension of the semistandard-tableau sum. This handles shapes outside the alphabet height.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 15, Proposition 2.12

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Proposition 2.12, arXiv:1501.05028v1, PDF p.15. The unrestricted zero extension is essential: restricting lambda to height≤d would erase the theorem. -/
theorem schur_excess_height_zero
    (lambda : YoungDiagram) (d : ℕ) (hheight : d < lambda.colLen 0) :
    extendedSchurPolynomial d lambda = 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
