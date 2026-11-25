-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_eq_sum_d4330b1b5c31
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_eq_sum_d4330b1b5c31
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:42:33.955237+00:00
-- url     : https://prove2.me/theorems/ce26da6d-c023-40d4-a8f5-f01bc8173ee7
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Length Decomp length eq sum d4330b1b5c31: P2 M Ground Theory Heights  Heights Vertical Length Decomp length eq sum d4330b1b5c31
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Length Decomp length eq sum d4330b1b5c31 construction uses the P2 M Ground Theory Heights  Heights Vertical Length Decomp length eq sum d4330b1b5c31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PLengthDecomp.lean#L86-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PLengthDecomp.lean#L86-L110

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_eq_sum_d4330b1b5c31 [Fintype (MaximalSpectrum B)] (hN : IsFiniteLength B N) :
    length R N = ∑ n : MaximalSpectrum B,
      length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl N) *
        length R (B ⧸ n.asIdeal) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«LengthDecomp».«length_eq_sum» := P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_eq_sum_d4330b1b5c31
