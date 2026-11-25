-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_deg_41b34c625bf3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_deg_41b34c625bf3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:10.86288+00:00
-- url     : https://prove2.me/theorems/e95eef7a-49cf-4567-a2f1-a9da0447b193
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota deg 41b34c625bf3: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota deg 41b34c625bf3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota deg 41b34c625bf3 construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota deg 41b34c625bf3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L264-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L264-L272

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_deg_41b34c625bf3 (c : ℤ) (I : StdCell N) :
    (degLoc (polyGraded S N) c I).map (iota I) = laurentDeg S N c I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«iota_deg» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_deg_41b34c625bf3
