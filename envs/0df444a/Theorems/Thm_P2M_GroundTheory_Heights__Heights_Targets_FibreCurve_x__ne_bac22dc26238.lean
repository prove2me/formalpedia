-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_x__ne_bac22dc26238
-- name    : P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_x__ne_bac22dc26238
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:32.715275+00:00
-- url     : https://prove2.me/theorems/38928801-dca4-56c3-990c-fceabd4eeb09
-- title:
--   P2 M Ground Theory Heights  Heights Targets Fibre Curve x  ne bac22dc26238: P2 M Ground Theory Heights  Heights Targets Fibre Curve x  ne bac22dc26238
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Fibre Curve x  ne bac22dc26238 construction uses the P2 M Ground Theory Heights  Heights Targets Fibre Curve x  ne bac22dc26238 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/FibreCurve.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/FibreCurve.lean#L53-L54

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

theorem P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_x__ne_bac22dc26238 {u : Ω} (hu : u ≠ 0) (p : Σ k, B2 k) : (gen u).x' p ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«FibreCurve».«x'_ne» := P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_x__ne_bac22dc26238
