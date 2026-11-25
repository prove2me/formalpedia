-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartModel_proof_96ab924230eb
-- name    : P2M_GroundTheory_Heights__Heights_GoodChartModel_proof_96ab924230eb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:29:16.007926+00:00
-- url     : https://prove2.me/theorems/361825a6-6fe5-42a7-a443-4e633317eb75
-- title:
--   P2 M Ground Theory Heights  Heights Good Chart Model proof 96ab924230eb: P2 M Ground Theory Heights  Heights Good Chart Model proof 96ab924230eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Chart Model proof 96ab924230eb construction uses the P2 M Ground Theory Heights  Heights Good Chart Model proof 96ab924230eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartModel.lean#L85-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartModel.lean#L85-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_ConeAvoidsFinite_proof_1e0c84911ab6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjHomInjective_proof_a56a3c2f38d9
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_rel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre segre_rel)
open ComplexSets MvPolynomial Matrix

theorem P2M_GroundTheory_Heights__Heights_GoodChartModel_proof_96ab924230eb (hZ : GoodChartZeroSet.Statement) (hD : GoodChartDim.Statement) :
    GoodChartModel.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodChartModel».«proof» := P2M_GroundTheory_Heights__Heights_GoodChartModel_proof_96ab924230eb
