-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_isMultiHomogIdeal_3254568b8d6d
-- name    : P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_isMultiHomogIdeal_3254568b8d6d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:47:08.4288+00:00
-- url     : https://prove2.me/theorems/f6d1fc5f-21c9-5fa8-959a-aae866d4eaba
-- title:
--   P2 M Ground Theory Heights  Heights Targets Fibre Curve is Multi Homog Ideal 3254568b8d6d: P2 M Ground Theory Heights  Heights Targets Fibre Curve is Multi Homog Ideal 3254568b8d6d
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Fibre Curve is Multi Homog Ideal 3254568b8d6d construction uses the P2 M Ground Theory Heights  Heights Targets Fibre Curve is Multi Homog Ideal 3254568b8d6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/FibreCurve.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/FibreCurve.lean#L39-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_QuotientMapImageZInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_FibreCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CoordinateConeArithVar_isMultiHomogIdeal_e52032a6c383

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

theorem P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_isMultiHomogIdeal_3254568b8d6d (u : Ω) : IsMultiHomogIdeal (mCoordIdeal (pt u)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«FibreCurve».«isMultiHomogIdeal» := P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_isMultiHomogIdeal_3254568b8d6d
