-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_localValuationResidueEvaluation_ker
-- name    : QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localValuationResidueEvaluation_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:06:40.512951+00:00
-- url     : https://prove2.me/theorems/df1a5221-bfdd-47c5-8c80-da2cdd403d3c
-- title:
--   Local Meromorphic Differential: local Valuation Residue Evaluation ker
-- statement:
--   The actual residue evaluation kernel is the valuation-ring maximal ideal, by positive local order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicValuationDifferentials.lean#L45-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicValuationDifferentials.lean#L45-L51

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalKaehlerCyclic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalMeromorphicDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicValuationDifferentials
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (K : Type*) [Field K] [Algebra ℂ K] (a : ℂ)
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary001
variable [Algebra K (MeromorphicGermRing a)] [IsScalarTower ℂ K (MeromorphicGermRing a)]
local notation "V" => localValuationRing K a
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary002
attribute [local instance] QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.MeromorphicValuationDifferentialsDictionary003

theorem QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localValuationResidueEvaluation_ker :
    RingHom.ker (localValuationResidueEvaluation K a) = IsLocalRing.maximalIdeal V := by sorry
