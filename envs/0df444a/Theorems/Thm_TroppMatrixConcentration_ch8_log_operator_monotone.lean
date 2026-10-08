-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch8_log_operator_monotone
-- name    : TroppMatrixConcentration.ch8_log_operator_monotone
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:53:36.202344+00:00
-- url     : https://prove2.me/theorems/4ef30a85-7686-46de-8f27-b9ab06efd793
-- title:
--   Proposition 8.4.4 — Logarithm is operator monotone
-- statement:
--   For positive-definite complex matrices $A,H$ of the same positive dimension,
--   $$A\preceq H\quad\Longrightarrow\quad\log A\preceq\log H.$$
--   The logarithm preserves semidefinite order on its positive-definite domain. This deterministic comparison is used in the matrix moment-generating-function arguments.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Proposition 8.4.4, printed p. 128.

import Definitions.Def_TroppMatrixConcentration_ch8_entropy

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch8_log_operator_monotone {d : ℕ} [NeZero d]
    (A H : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosDef) (hH : H.PosDef)
    (hAH : loewnerLE A H) :
    loewnerLE (matrixLog A) (matrixLog H) := by sorry

end TroppMatrixConcentration
