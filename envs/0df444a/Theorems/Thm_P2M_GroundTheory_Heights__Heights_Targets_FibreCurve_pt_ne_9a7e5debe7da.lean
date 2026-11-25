-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_pt_ne_9a7e5debe7da
-- name    : P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_pt_ne_9a7e5debe7da
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:21.234482+00:00
-- url     : https://prove2.me/theorems/3351be8a-5ef4-5cab-a9d4-01cc822577f1
-- title:
--   P2 M Ground Theory Heights  Heights Targets Fibre Curve pt ne 9a7e5debe7da: P2 M Ground Theory Heights  Heights Targets Fibre Curve pt ne 9a7e5debe7da
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Fibre Curve pt ne 9a7e5debe7da construction uses the P2 M Ground Theory Heights  Heights Targets Fibre Curve pt ne 9a7e5debe7da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/FibreCurve.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/FibreCurve.lean#L24-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_QuotientMapImageZInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_FibreCurve
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets GroundTheory.Heights₂.Heights.Targets.FibreCurve
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_pt_ne_9a7e5debe7da {u : Ω} (hu : u ≠ 0) (p : Σ k, B2 k) : pt u p ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«FibreCurve».«pt_ne» := P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_pt_ne_9a7e5debe7da
