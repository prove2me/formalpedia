-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_gen_mem_9183a2006dec
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_gen_mem_9183a2006dec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:34.225059+00:00
-- url     : https://prove2.me/theorems/0a6c9713-bcd5-4626-9d26-e8e54dc73968
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota gen mem 9183a2006dec: P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota gen mem 9183a2006dec
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota gen mem 9183a2006dec construction uses the P2 M Ground Theory Heights  Heights Kleiman Laurent Loc iota gen mem 9183a2006dec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L204-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerrePolyLaurent.lean#L204-L232

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_gen_mem_9183a2006dec (c : ℤ) (I : StdCell N) (m : Poly S N) (s : monos (S := S) I.1) (a : ℤ) (e : ℕ)
    (hm : m ∈ (polyGraded S N).piece a) (hs : (s : Poly S N).IsHomogeneous e) (hc : a - e = c) :
    iota I (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I.1) (Poly S N)) ∈
      laurentDeg S N c I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LaurentLoc».«iota_gen_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_gen_mem_9183a2006dec
