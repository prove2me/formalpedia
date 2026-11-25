-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh___cupH_right_90f73d584671
-- name    : P2M_GroundTheory_GroupCoh___cupH_right_90f73d584671
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:48:16.218685+00:00
-- url     : https://prove2.me/theorems/316e7ce5-d42f-4a74-9b4e-998c10e462b2
-- title:
--   P2 M Ground Theory Group Coh   cup H right 90f73d584671: P2 M Ground Theory Group Coh   cup H right 90f73d584671
-- statement:
--   The P2 M Ground Theory Group Coh   cup H right 90f73d584671 construction uses the P2 M Ground Theory Group Coh   cup H right 90f73d584671 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L119-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L119-L138

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

theorem P2M_GroundTheory_GroupCoh___cupH_right_90f73d584671 (hBX : (X.map (tensorLeft B)).ShortExact) {p q n : ℕ} (h : q + p = n)
    (h' : q + (p + 1) = n + 1) (b : groupCohomology B q) (a : groupCohomology X.X₃ p) :
    δ hBX n (n + 1) rfl (cupH h b a) = (-1 : k) ^ q • cupH h' b (δ hX p (p + 1) rfl a) := by sorry

alias «GroundTheory».«GroupCoh».«δ_cupH_right» := P2M_GroundTheory_GroupCoh___cupH_right_90f73d584671
