-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P36_three_eigenvalue_example
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P36.three_eigenvalue_example
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:16:15.569188+00:00
-- url     : https://prove2.me/theorems/3af5f4a0-b672-403f-89de-beb2d6932f22
-- title:
--   Example 27: exact CB norm for the three-eigenvalue example
-- statement:
--   Let
--
--   $$U=\operatorname{diag}\!\left(e^{5\pi i/4},e^{\pi i},e^{3\pi i/4}\right),\qquad \phi(X)=U^\dagger XU-X\quad(X\in M_3).$$
--
--   Then the completely bounded norm, defined from Euclidean operator norms and all positive finite amplifications, is
--
--   $$\|\phi\|_{\rm cb}=\sqrt2.$$
--
--   This is the exact mathematical value used to assess the numerical example. It makes no assertion that a particular finite random sample always returns a prescribed estimate or runtime.
-- source:
--   Computing Stabilized Norms for Quantum Operations via the Theory of Completely Bounded Maps, arXiv:0711.3636v1, PDF p. 19, Example 27: exact norm in the three-eigenvalue example

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P36

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P36

local notation "Mat" => QAlgorithms.Papers.Independent.Information100.P50.M

local notation "Map" => QAlgorithms.Papers.Independent.Information100.P50.Lin

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

/-- Example 27, PDF p.19: reversed conjugation U-adjoint X U; the exact norm
is sqrt(2), independently of any empirical random-sampling output or timing. -/
theorem three_eigenvalue_example :
    extendedCBNorm (unitaryDifference exampleUnitaryᴴ) = ENNReal.ofReal (Real.sqrt 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P36

end
