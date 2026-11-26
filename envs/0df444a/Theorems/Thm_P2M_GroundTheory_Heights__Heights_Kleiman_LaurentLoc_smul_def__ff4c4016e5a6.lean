-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_smul_def__ff4c4016e5a6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_smul_def__ff4c4016e5a6
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:26:42.285626+00:00
-- url     : https://prove2.me/theorems/3e6abc24-b132-5c11-ac56-79c35450d8b5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc smul def  ff4c4016e5a6: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc smul def  ff4c4016e5a6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc smul def  ff4c4016e5a6 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc smul def  ff4c4016e5a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L83-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L83-L83

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_smul_def__ff4c4016e5a6 (p : Poly S N) (x : LRing S N) : p • x = toL S N p * x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«smul_def'» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_smul_def__ff4c4016e5a6
