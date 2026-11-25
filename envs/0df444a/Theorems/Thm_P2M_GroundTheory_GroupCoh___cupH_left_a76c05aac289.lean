-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh___cupH_left_a76c05aac289
-- name    : P2M_GroundTheory_GroupCoh___cupH_left_a76c05aac289
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:51.020637+00:00
-- url     : https://prove2.me/theorems/aaf9d120-09be-439b-bd93-cab36e0fe7fb
-- title:
--   P2 M Ground Theory Group Coh   cup H left a76c05aac289: P2 M Ground Theory Group Coh   cup H left a76c05aac289
-- statement:
--   The P2 M Ground Theory Group Coh   cup H left a76c05aac289 construction uses the P2 M Ground Theory Group Coh   cup H left a76c05aac289 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L99-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupConnecting.lean#L99-L117

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

theorem P2M_GroundTheory_GroupCoh___cupH_left_a76c05aac289 (hXB : (X.map (tensorRight B)).ShortExact) {p q n : ℕ} (h : p + q = n)
    (h' : p + 1 + q = n + 1) (a : groupCohomology X.X₃ p) (b : groupCohomology B q) :
    δ hXB n (n + 1) rfl (cupH h a b) = cupH h' (δ hX p (p + 1) rfl a) b := by sorry

alias «GroundTheory».«GroupCoh».«δ_cupH_left» := P2M_GroundTheory_GroupCoh___cupH_left_a76c05aac289
