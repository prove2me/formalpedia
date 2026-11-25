-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh____augTrivSES_res_ac40718a115e
-- name    : P2M_GroundTheory_GroupCoh____augTrivSES_res_ac40718a115e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:01:37.961817+00:00
-- url     : https://prove2.me/theorems/04298cc8-f75b-5789-aab8-a0f1c0cf3651
-- title:
--   P2 M Ground Theory Group Coh    aug Triv SES res ac40718a115e: P2 M Ground Theory Group Coh    aug Triv SES res ac40718a115e
-- statement:
--   The P2 M Ground Theory Group Coh    aug Triv SES res ac40718a115e construction uses the P2 M Ground Theory Group Coh    aug Triv SES res ac40718a115e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugTrivial.lean#L122-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugTrivial.lean#L122-L132

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_AugTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable (k G : Type u) [CommRing k] [Group G]
variable {k G}
variable (k) {H : Type u} [Group H] (φ : H →* G)

theorem P2M_GroundTheory_GroupCoh____augTrivSES_res_ac40718a115e :
    δ (augTrivSES_res_shortExact k φ) 0 1 rfl ((H0Iso _).inv (oneInvariant k φ)) =
      H1π _ (augCocycle k φ) := by sorry

alias «GroundTheory».«GroupCoh».«δ₀_augTrivSES_res» := P2M_GroundTheory_GroupCoh____augTrivSES_res_ac40718a115e
