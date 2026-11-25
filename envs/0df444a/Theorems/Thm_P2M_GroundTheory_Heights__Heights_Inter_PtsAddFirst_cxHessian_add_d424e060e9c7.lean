-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_cxHessian_add_d424e060e9c7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_cxHessian_add_d424e060e9c7
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:42:29.141495+00:00
-- url     : https://prove2.me/theorems/7b38f406-603d-4ae9-a7a9-5b3ed5ae7a45
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pts Add First cx Hessian add d424e060e9c7: P2 M Ground Theory Heights  Heights Inter Pts Add First cx Hessian add d424e060e9c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pts Add First cx Hessian add d424e060e9c7 construction uses the P2 M Ground Theory Heights  Heights Inter Pts Add First cx Hessian add d424e060e9c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsAddFirst.lean#L13-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsAddFirst.lean#L13-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAddFirst
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_cxHessian_add_d424e060e9c7 {D : ℕ} {a b ψ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 a y') (hb : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 b y')
    (hψ : ψ =ᶠ[𝓝 y] fun y' => a y' + b y') :
    cxHessian ψ y = cxHessian a y + cxHessian b y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PtsAddFirst».«cxHessian_add» := P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_cxHessian_add_d424e060e9c7
