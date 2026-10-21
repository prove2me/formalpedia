-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_proposition_1_1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.proposition_1_1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:38:45.696299+00:00
-- url     : https://prove2.me/theorems/04b38573-9d4c-47ed-9354-0ebbbac54537
-- title:
--   Proposition 1.1
-- statement:
--   Let $A,B$ be strictly positive complex matrices on a finite-dimensional space and let $0\le s\le1$. With $|M|=(M^*M)^{1/2}$ and ordinary matrix trace,
--
--   $$\frac{\operatorname{Tr} A+\operatorname{Tr} B-\operatorname{Tr}|A-B|}{2}\le\operatorname{Tr}(A^{1-s}B^s).$$
--
--   This trace inequality supplies the finite quantum Chernoff upper bound. The zero-dimensional matrix case is included.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 4, Proposition 1.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 1.1, arXiv:1109.3804v2, PDF p.4, (1.1). -/
theorem proposition_1_1 {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.PosDef) (hB : B.PosDef)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (A.trace.re + B.trace.re - QAlgorithms.traceNorm (A - B)) / 2 ≤
      (positiveMatrixRpow A (1 - s) * positiveMatrixRpow B s).trace.re := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
