-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_finite_maximalSpectrum_0d05a3129625
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_finite_maximalSpectrum_0d05a3129625
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:50.741906+00:00
-- url     : https://prove2.me/theorems/5703d105-0c11-58cd-b003-7731146f5bc1
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Length Decomp finite maximal Spectrum 0d05a3129625: P2 M Ground Theory Heights  Heights Vertical Length Decomp finite maximal Spectrum 0d05a3129625
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Length Decomp finite maximal Spectrum 0d05a3129625 construction uses the P2 M Ground Theory Heights  Heights Vertical Length Decomp finite maximal Spectrum 0d05a3129625 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PLengthDecomp.lean#L112-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PLengthDecomp.lean#L112-L120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PLengthDecomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open Module IsLocalRing LinearMap Submodule
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.LengthDecomp
open Classical
variable {B : Type*} [CommRing B]
variable {R : Type*} [CommRing R] [Algebra R B]
variable {N : Type*} [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]

theorem P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_finite_maximalSpectrum_0d05a3129625 [IsLocalRing R] [Module.Finite R B] :
    Finite (MaximalSpectrum B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«LengthDecomp».«finite_maximalSpectrum» := P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_finite_maximalSpectrum_0d05a3129625
