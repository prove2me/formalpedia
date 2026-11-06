-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_meromorphicNoPoleEvaluation_eq_zero_iff_order_pos
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.meromorphicNoPoleEvaluation_eq_zero_iff_order_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:04:57.370875+00:00
-- url     : https://prove2.me/theorems/cac9a76f-1c90-452e-97b1-3ada7a3c5cf2
-- title:
--   Meromorphic Germs: meromorphic No Pole Evaluation eq zero iff order pos
-- statement:
--   The Meromorphic Germs construction uses the meromorphic No Pole Evaluation eq zero iff order pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AnalyticGermEvaluation.lean#L118-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AnalyticGermEvaluation.lean#L118-L132

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
import Mathlib.Topology.Instances.Complex
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.meromorphicNoPoleEvaluation_eq_zero_iff_order_pos
    (x : ℂ) (A : (AddValuation.toValuation (meromorphicOrderValuation x)).integer) :
    meromorphicNoPoleEvaluation x A = 0 ↔ 0 < meromorphicOrderValuation x A.val := by sorry
