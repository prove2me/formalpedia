-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_x_ne_1d15c2be2ae8
-- name    : P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_x_ne_1d15c2be2ae8
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:41:16.492796+00:00
-- url     : https://prove2.me/theorems/63a4e7da-dcdd-549e-8e26-2288a283624d
-- title:
--   P2 M Ground Theory Heights  Heights Targets Fibre Curve x ne 1d15c2be2ae8: P2 M Ground Theory Heights  Heights Targets Fibre Curve x ne 1d15c2be2ae8
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Fibre Curve x ne 1d15c2be2ae8 construction uses the P2 M Ground Theory Heights  Heights Targets Fibre Curve x ne 1d15c2be2ae8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/FibreCurve.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/FibreCurve.lean#L56-L59

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

theorem P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_x_ne_1d15c2be2ae8 {u : Ω} (hu : u ≠ 0) (p : Σ k, B1 k) : (gen u).x p ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«FibreCurve».«x_ne» := P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_x_ne_1d15c2be2ae8
