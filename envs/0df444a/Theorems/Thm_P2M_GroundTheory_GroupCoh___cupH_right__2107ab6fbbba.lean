-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh___cupH_right__2107ab6fbbba
-- name    : P2M_GroundTheory_GroupCoh___cupH_right__2107ab6fbbba
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:55:27.36091+00:00
-- url     : https://prove2.me/theorems/62ce5d07-825b-4ed5-a3e6-c3917b041d92
-- title:
--   P2 M Ground Theory Group Coh   cup H right  2107ab6fbbba: P2 M Ground Theory Group Coh   cup H right  2107ab6fbbba
-- statement:
--   The P2 M Ground Theory Group Coh   cup H right  2107ab6fbbba construction uses the P2 M Ground Theory Group Coh   cup H right  2107ab6fbbba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L147-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L147-L152

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

theorem P2M_GroundTheory_GroupCoh___cupH_right__2107ab6fbbba (hBX : (X.map (tensorLeft B)).ShortExact) {p q n p' m : ℕ}
    (hp : p + 1 = p') (hm : n + 1 = m) (h : q + p = n) (h' : q + p' = m)
    (b : groupCohomology B q) (a : groupCohomology X.X₃ p) :
    δ hBX n m hm (cupH h b a) = (-1 : k) ^ q • cupH h' b (δ hX p p' hp a) := by sorry

alias «GroundTheory».«GroupCoh».«δ_cupH_right'» := P2M_GroundTheory_GroupCoh___cupH_right__2107ab6fbbba
