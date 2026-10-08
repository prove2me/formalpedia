-- Prove2me | Theorems.Thm_TroppMatrixConcentration_ch8_log_operator_concave
-- name    : TroppMatrixConcentration.ch8_log_operator_concave
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:52:37.476643+00:00
-- url     : https://prove2.me/theorems/f59f5c41-e016-4a04-b9c8-72f03cff1f1c
-- title:
--   Proposition 8.4.8 — Logarithm is operator concave
-- statement:
--   The negative logarithm is operator convex on the positive real line. Equivalently, for positive-definite complex matrices $A,H$ of any common positive finite dimension and $0\le t\le1$,
--   $$t\log A+(1-t)\log H\preceq\log(tA+(1-t)H).$$
--   This is concavity in semidefinite order, with no assumption that $A$ and $H$ commute.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Proposition 8.4.8, printed pp. 130–131.

import Definitions.Def_TroppMatrixConcentration_ch8_entropy

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem ch8_log_operator_concave :
    ch8_operatorConvexOn (Set.Ioi 0) (fun x => -Real.log x) := by sorry

end TroppMatrixConcentration
