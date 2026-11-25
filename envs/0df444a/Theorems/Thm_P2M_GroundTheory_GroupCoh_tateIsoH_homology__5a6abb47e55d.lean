-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateIsoH_homology__5a6abb47e55d
-- name    : P2M_GroundTheory_GroupCoh_tateIsoH_homology__5a6abb47e55d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:54:37.010242+00:00
-- url     : https://prove2.me/theorems/32069ae7-4eb1-480b-a024-07bc9fa7fb93
-- title:
--   P2 M Ground Theory Group Coh tate Iso H homology  5a6abb47e55d: P2 M Ground Theory Group Coh tate Iso H homology  5a6abb47e55d
-- statement:
--   The P2 M Ground Theory Group Coh tate Iso H homology  5a6abb47e55d construction uses the P2 M Ground Theory Group Coh tate Iso H homology  5a6abb47e55d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean#L42-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean#L42-L52

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

theorem P2M_GroundTheory_GroupCoh_tateIsoH_homology__5a6abb47e55d (A : Rep k G) (n : ℕ) [NeZero n] (z : (tateComplex A).cycles n) :
    (tateIsoH A n n rfl).hom.hom (((tateComplex A).homologyπ n).hom z) =
      π A n (cocyclesMk (((tateComplex A).iCycles n).hom z) (tate_d_iCycles A n z)) := by sorry

alias «GroundTheory».«GroupCoh».«tateIsoH_homologyπ» := P2M_GroundTheory_GroupCoh_tateIsoH_homology__5a6abb47e55d
