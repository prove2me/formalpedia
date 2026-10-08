-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch8_entropy_nonnegative
-- name    : TroppMatrixConcentration.ch8_entropy_nonnegative
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:51:44.877667+00:00
-- url     : https://prove2.me/theorems/4080594a-02da-4437-9b6d-cd4bcac08161
-- title:
--   Proposition 8.1.3 — Matrix relative entropy is nonnegative
-- statement:
--   For any positive-definite complex matrices $A,H$ of the same positive dimension,
--   $$D(A;H)=\operatorname{tr}[A(\log A-\log H)-(A-H)]\ge0.$$
--   The matrices need not commute or have trace one. The corrected entropy used here provides the nonnegativity statement underlying the variational trace formula.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Proposition 8.1.3 and Section 8.3.5, printed pp. 120 and 126.

import Definitions.Def_TroppMatrixConcentration_ch8_entropy

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch8_entropy_nonnegative {d : ℕ} [NeZero d]
    (A H : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosDef) (hH : H.PosDef) :
    0 ≤ ch8_relativeEntropy A H := by sorry

end TroppMatrixConcentration
