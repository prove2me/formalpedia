-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_localizedModule_quotient_79d7d8dcab70
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_localizedModule_quotient_79d7d8dcab70
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:42:37.459798+00:00
-- url     : https://prove2.me/theorems/f831eb69-2c56-4184-acae-68d6dd658ed2
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Length Decomp length localized Module quotient 79d7d8dcab70: P2 M Ground Theory Heights  Heights Vertical Length Decomp length localized Module quotient 79
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Length Decomp length localized Module quotient 79d7d8dcab70 construction uses the P2 M Ground Theory Heights  Heights Vertical Length Decomp length localized Module quotient 79d7d8dcab70 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PLengthDecomp.lean#L26-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PLengthDecomp.lean#L26-L54

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_localizedModule_quotient_79d7d8dcab70 (n m : MaximalSpectrum B) :
    length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl (B ⧸ m.asIdeal)) =
      if n = m then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«LengthDecomp».«length_localizedModule_quotient» := P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_length_localizedModule_quotient_79d7d8dcab70
