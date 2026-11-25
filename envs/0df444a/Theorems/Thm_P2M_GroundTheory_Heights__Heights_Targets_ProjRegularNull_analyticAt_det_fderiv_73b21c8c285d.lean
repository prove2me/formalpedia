-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegularNull_analyticAt_det_fderiv_73b21c8c285d
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjRegularNull_analyticAt_det_fderiv_73b21c8c285d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:07:53.476002+00:00
-- url     : https://prove2.me/theorems/8ab61a64-2cfb-4b51-84ef-822e558ac2e8
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Regular Null analytic At det fderiv 73b21c8c285d: P2 M Ground Theory Heights  Heights Targets Proj Regular Null analytic At det fderiv 73b21c8c285d
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Regular Null analytic At det fderiv 73b21c8c285d construction uses the P2 M Ground Theory Heights  Heights Targets Proj Regular Null analytic At det fderiv 73b21c8c285d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularNull.lean#L15-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularNull.lean#L15-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularNull
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
open MvPolynomial MeasureTheory Filter Topology Metric ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Targets.ProjRegularNull

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjRegularNull_analyticAt_det_fderiv_73b21c8c285d {n : ℕ} {q : (Fin n → ℂ) → Fin n → ℂ} {u : Fin n → ℂ}
    (hq : AnalyticAt ℂ q u) :
    AnalyticAt ℂ (fun v => LinearMap.det (fderiv ℂ q v : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjRegularNull».«analyticAt_det_fderiv» := P2M_GroundTheory_Heights__Heights_Targets_ProjRegularNull_analyticAt_det_fderiv_73b21c8c285d
