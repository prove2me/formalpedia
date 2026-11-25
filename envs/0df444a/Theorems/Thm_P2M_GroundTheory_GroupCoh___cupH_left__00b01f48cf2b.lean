-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh___cupH_left__00b01f48cf2b
-- name    : P2M_GroundTheory_GroupCoh___cupH_left__00b01f48cf2b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:15:42.558813+00:00
-- url     : https://prove2.me/theorems/614bc782-7c97-53dc-8ae9-7c1852e8b365
-- title:
--   P2 M Ground Theory Group Coh   cup H left  00b01f48cf2b: P2 M Ground Theory Group Coh   cup H left  00b01f48cf2b
-- statement:
--   The P2 M Ground Theory Group Coh   cup H left  00b01f48cf2b construction uses the P2 M Ground Theory Group Coh   cup H left  00b01f48cf2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L140-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L140-L145

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
variable (B : Rep k G)

theorem P2M_GroundTheory_GroupCoh___cupH_left__00b01f48cf2b (hXB : (X.map (tensorRight B)).ShortExact) {p q n p' m : ℕ}
    (hp : p + 1 = p') (hm : n + 1 = m) (h : p + q = n) (h' : p' + q = m)
    (a : groupCohomology X.X₃ p) (b : groupCohomology B q) :
    δ hXB n m hm (cupH h a b) = cupH h' (δ hX p p' hp a) b := by sorry

alias «GroundTheory».«GroupCoh».«δ_cupH_left'» := P2M_GroundTheory_GroupCoh___cupH_left__00b01f48cf2b
