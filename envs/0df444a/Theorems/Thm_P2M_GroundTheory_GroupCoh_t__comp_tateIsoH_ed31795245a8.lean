-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_t__comp_tateIsoH_ed31795245a8
-- name    : P2M_GroundTheory_GroupCoh_t__comp_tateIsoH_ed31795245a8
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:54:32.159663+00:00
-- url     : https://prove2.me/theorems/c36437a6-b31a-4422-bbe5-c72d582fcfbc
-- title:
--   P2 M Ground Theory Group Coh t  comp tate Iso H ed31795245a8: P2 M Ground Theory Group Coh t  comp tate Iso H ed31795245a8
-- statement:
--   The P2 M Ground Theory Group Coh t  comp tate Iso H ed31795245a8 construction uses the P2 M Ground Theory Group Coh t  comp tate Iso H ed31795245a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean#L95-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean#L95-L127

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
set_option backward.isDefEq.respectTransparency false

theorem P2M_GroundTheory_GroupCoh_t__comp_tateIsoH_ed31795245a8 {S : ShortComplex (Rep k G)} (hS : S.ShortExact) (n : ℕ) [NeZero n] :
    tδ hS n (n + 1) rfl ≫ (tateIsoH S.X₁ (n + 1) (n + 1) (Nat.cast_succ n).symm).hom =
      (tateIsoH S.X₃ n n rfl).hom ≫ δ hS n (n + 1) rfl := by sorry

alias «GroundTheory».«GroupCoh».«tδ_comp_tateIsoH» := P2M_GroundTheory_GroupCoh_t__comp_tateIsoH_ed31795245a8
