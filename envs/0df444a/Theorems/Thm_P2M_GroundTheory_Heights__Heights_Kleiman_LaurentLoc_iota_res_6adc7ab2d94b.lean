-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_res_6adc7ab2d94b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_res_6adc7ab2d94b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:39.659517+00:00
-- url     : https://prove2.me/theorems/60ee0670-6651-45f9-bc33-7ae76e2fbb27
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota res 6adc7ab2d94b: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota res 6adc7ab2d94b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota res 6adc7ab2d94b construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota res 6adc7ab2d94b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L183-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L183-L191

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_res_6adc7ab2d94b (I J : StdCell N) (h : I.1 ⊆ J.1) (z : LocMod S N (Poly S N) I.1) :
    iota J (locResS I J h z) = iota I z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«iota_res» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_res_6adc7ab2d94b
