-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_det_fderiv_div_5c6db1de3544
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_det_fderiv_div_5c6db1de3544
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:27:26.316531+00:00
-- url     : https://prove2.me/theorems/9f6903fb-79c0-4095-87b7-45a7b313bd7b
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Regular Closure Open det fderiv div 5c6db1de3544: P2 M Ground Theory Heights  Heights Targets Proj Regular Closure Open det fderiv div 5c6db1de3544
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Regular Closure Open det fderiv div 5c6db1de3544 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Regular Closure Open det fderiv div 5c6db1de3544 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularClosureOpen.lean#L31-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRegularClosureOpen.lean#L31-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularClosureOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegularClosureOpen
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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Targets.ProjRegularClosureOpen

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_det_fderiv_div_5c6db1de3544 {n : ℕ} {F : (Fin n → ℂ) → Fin (n + 1) → ℂ} {u : Fin n → ℂ}
    (hF : AnalyticAt ℂ F u) (h0 : F u 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (fun v (i : Fin n) => F v i.succ / F v 0) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = ((F u 0 ^ 2)⁻¹) ^ n * (projNumMat F u).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjRegularClosureOpen».«det_fderiv_div» := P2M_GroundTheory_Heights__Heights_Targets_ProjRegularClosureOpen_det_fderiv_div_5c6db1de3544
