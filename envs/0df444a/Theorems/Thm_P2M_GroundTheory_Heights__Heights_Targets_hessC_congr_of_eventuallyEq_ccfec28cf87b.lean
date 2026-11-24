-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_hessC_congr_of_eventuallyEq_ccfec28cf87b
-- name    : P2M_GroundTheory_Heights__Heights_Targets_hessC_congr_of_eventuallyEq_ccfec28cf87b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:24.482649+00:00
-- url     : https://prove2.me/theorems/85c2b07c-cb9d-4b85-adeb-112e7887932d
-- title:
--   P2 M Ground Theory Heights  Heights Targets hess C congr of eventually Eq ccfec28cf87b: P2 M Ground Theory Heights  Heights Targets hess C congr of eventually Eq ccfec28cf87b
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets hess C congr of eventually Eq ccfec28cf87b construction uses the P2 M Ground Theory Heights  Heights Targets hess C congr of eventually Eq ccfec28cf87b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRankDropDens.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRankDropDens.lean#L16-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRankDropDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRankDropDens
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

theorem P2M_GroundTheory_Heights__Heights_Targets_hessC_congr_of_eventuallyEq_ccfec28cf87b {D : ℕ} {φ ψ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : φ =ᶠ[𝓝 z] ψ) : ReciprocityTheory.AnForm.hessC φ z = ReciprocityTheory.AnForm.hessC ψ z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«hessC_congr_of_eventuallyEq» := P2M_GroundTheory_Heights__Heights_Targets_hessC_congr_of_eventuallyEq_ccfec28cf87b
