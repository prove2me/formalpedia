-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P57_positive_trace_inequality
-- name    : QAlgorithms.Papers.Independent.Intake100.P57.positive_trace_inequality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:01:21.623891+00:00
-- url     : https://prove2.me/theorems/f55f7ca7-d9fe-4bcd-9766-aeca87333834
-- title:
--   A trace inequality for positive operators on different spaces
-- statement:
--   Let $X$ and $Y$ be positive semidefinite operators on two finite-dimensional Hilbert spaces, which may differ. They need not be normalized. Suppose $\operatorname{Tr}X=\operatorname{Tr}\sqrt Y$, where the square root is the positive semidefinite spectral square root. Then
--
--   $$
--   \operatorname{Tr}X^2\ge\frac{(\operatorname{Tr}Y)^3}{\operatorname{rank}(X)\,\operatorname{Tr}Y^2}.
--   $$
--
--   At $Y=0$, the hypothesis forces $X=0$ and the closed inequality is interpreted as $0\ge0$. This finite-dimensional trace inequality is the technical estimate used for the paper's general PGM bound.
--
--   **Formalization Note** Real traces are used on positive semidefinite matrices, and total real division assigns zero to the zero numerator/denominator boundary.
-- source:
--   Simplified instantaneous non-local quantum computation with applications to position-based cryptography, arXiv:1101.1065v3, PDF p. 16, A.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P57

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P57

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- P34 uses half the channel distance. Every occurrence below is multiplied by two.

open QAlgorithms.Papers.Independent.Information100.P34 (diamondDistance)

open QAlgorithms.Papers.Independent.Dependency50.P07 (ensembleMean)

/-- Lemma A.2, PDF p.16, (A6). The hypothesis contains the PSD square root
of Y. The operators may act on different finite spaces and need not be states.
At Y=0 the closed formula is read with 0/0=0, consistently with X=0. -/
theorem positive_trace_inequality {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (X : Matrix I I ℂ) (Y : Matrix J J ℂ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htrace : X.trace.re = (cfc Real.sqrt Y).trace.re) :
    Y.trace.re ^ 3 / ((Matrix.rank X : ℝ) * (Y^2).trace.re) ≤
      (X^2).trace.re := by sorry

end QAlgorithms.Papers.Independent.Intake100.P57

end
