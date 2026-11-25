-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_linPoly_eq_mulVec_37d28054619f
-- name    : P2M_GroundTheory_Heights__Heights_eval_linPoly_eq_mulVec_37d28054619f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T16:50:07.912415+00:00
-- url     : https://prove2.me/theorems/8d9cada3-4634-55e5-9897-698bbecb6116
-- title:
--   P2 M Ground Theory Heights  Heights eval lin Poly eq mul Vec 37d28054619f: P2 M Ground Theory Heights  Heights eval lin Poly eq mul Vec 37d28054619f
-- statement:
--   The P2 M Ground Theory Heights  Heights eval lin Poly eq mul Vec 37d28054619f construction uses the P2 M Ground Theory Heights  Heights eval lin Poly eq mul Vec 37d28054619f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartProjFinite.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartProjFinite.lean#L25-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartProjFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartProjFinite
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

theorem P2M_GroundTheory_Heights__Heights_eval_linPoly_eq_mulVec_37d28054619f {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (r : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly A r) = (A *ᵥ x) r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eval_linPoly_eq_mulVec» := P2M_GroundTheory_Heights__Heights_eval_linPoly_eq_mulVec_37d28054619f
