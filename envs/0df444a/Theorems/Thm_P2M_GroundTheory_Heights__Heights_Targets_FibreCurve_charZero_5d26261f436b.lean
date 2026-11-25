-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_charZero_5d26261f436b
-- name    : P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_charZero_5d26261f436b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:16.727789+00:00
-- url     : https://prove2.me/theorems/36a98d74-1d4e-4db1-88ec-f4f815eebf54
-- title:
--   P2 M Ground Theory Heights  Heights Targets Fibre Curve char Zero 5d26261f436b: P2 M Ground Theory Heights  Heights Targets Fibre Curve char Zero 5d26261f436b
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Fibre Curve char Zero 5d26261f436b construction uses the P2 M Ground Theory Heights  Heights Targets Fibre Curve char Zero 5d26261f436b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/FibreCurve.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/FibreCurve.lean#L45-L51

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

theorem P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_charZero_5d26261f436b [CharZero Ω] (u : Ω) : CharZero (gen u).Φ' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«FibreCurve».«charZero» := P2M_GroundTheory_Heights__Heights_Targets_FibreCurve_charZero_5d26261f436b
