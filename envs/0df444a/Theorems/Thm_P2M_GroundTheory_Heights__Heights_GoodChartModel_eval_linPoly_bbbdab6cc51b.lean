-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartModel_eval_linPoly_bbbdab6cc51b
-- name    : P2M_GroundTheory_Heights__Heights_GoodChartModel_eval_linPoly_bbbdab6cc51b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:25:13.689662+00:00
-- url     : https://prove2.me/theorems/74393966-1835-4c77-a0d9-f3a5c603d425
-- title:
--   P2 M Ground Theory Heights  Heights Good Chart Model eval lin Poly bbbdab6cc51b: P2 M Ground Theory Heights  Heights Good Chart Model eval lin Poly bbbdab6cc51b
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Chart Model eval lin Poly bbbdab6cc51b construction uses the P2 M Ground Theory Heights  Heights Good Chart Model eval lin Poly bbbdab6cc51b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartModel.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartModel.lean#L28-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartModel
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
open GroundTheory.Heights₂.Heights.GoodChartModel

theorem P2M_GroundTheory_Heights__Heights_GoodChartModel_eval_linPoly_bbbdab6cc51b {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (r : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly A r) = (A *ᵥ x) r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodChartModel».«eval_linPoly» := P2M_GroundTheory_Heights__Heights_GoodChartModel_eval_linPoly_bbbdab6cc51b
