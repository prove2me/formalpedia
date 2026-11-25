-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_injective_a95770eb2fe4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_injective_a95770eb2fe4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:23.577723+00:00
-- url     : https://prove2.me/theorems/cc6cf58b-538a-4d97-9426-28f89fb723f9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc localization To Laurent injective a95770eb2fe4: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc localization To Laurent injective a95770
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc localization To Laurent injective a95770eb2fe4 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc localization To Laurent injective a95770eb2fe4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L113-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L113-L120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable (S : Type u) [CommRing S] (N : ℕ)
variable {S N}
attribute [local instance] algP

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_injective_a95770eb2fe4 (I : Finset (Fin (N + 1))) : Function.Injective (iotaP (S := S) (N := N) I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«localizationToLaurent_injective» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_injective_a95770eb2fe4
