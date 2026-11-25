-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_image_exps_fbf5ec376f1c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_image_exps_fbf5ec376f1c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:27.175368+00:00
-- url     : https://prove2.me/theorems/73726c71-e944-42a6-b91f-712c7808a817
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc image exps fbf5ec376f1c: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc image exps fbf5ec376f1c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc image exps fbf5ec376f1c construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc image exps fbf5ec376f1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L145-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L145-L156

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
variable {S : Type u} [CommRing S] {N : ℕ}
attribute [local instance] algP

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_image_exps_fbf5ec376f1c (c : ℤ) :
    expToInt N '' {d | Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) d = c} = laurentExps N c ∅ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«image_exps» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_image_exps_fbf5ec376f1c
