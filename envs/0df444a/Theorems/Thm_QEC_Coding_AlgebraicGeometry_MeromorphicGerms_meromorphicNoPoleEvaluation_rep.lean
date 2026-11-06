-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_meromorphicNoPoleEvaluation_rep
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.meromorphicNoPoleEvaluation_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:04:47.109498+00:00
-- url     : https://prove2.me/theorems/2ffa477a-6d66-4c1a-aa29-f5af4197d2d4
-- title:
--   Meromorphic Germs: meromorphic No Pole Evaluation rep
-- statement:
--   The Meromorphic Germs construction uses the meromorphic No Pole Evaluation rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AnalyticGermEvaluation.lean#L111-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AnalyticGermEvaluation.lean#L111-L116

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
import Mathlib.Topology.Instances.Complex
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.meromorphicNoPoleEvaluation_rep (x : ℂ)
    (A : (AddValuation.toValuation (meromorphicOrderValuation x)).integer)
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f x)
    (he : A.val.val = (f : Germ (𝓝[≠] x) ℂ)) :
    meromorphicNoPoleEvaluation x A = f x := by sorry
