-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateIsoH_t__homology__77eebf810831
-- name    : P2M_GroundTheory_GroupCoh_tateIsoH_t__homology__77eebf810831
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:52:10.807454+00:00
-- url     : https://prove2.me/theorems/5b70e7af-76c4-58e7-bc5f-8d73bdd1a3c6
-- title:
--   P2 M Ground Theory Group Coh tate Iso H t  homology  77eebf810831: P2 M Ground Theory Group Coh tate Iso H t  homology  77eebf810831
-- statement:
--   The P2 M Ground Theory Group Coh tate Iso H t  homology  77eebf810831 construction uses the P2 M Ground Theory Group Coh tate Iso H t  homology  77eebf810831 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L386-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L386-L419

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G]
set_option backward.isDefEq.respectTransparency false

theorem P2M_GroundTheory_GroupCoh_tateIsoH_t__homology__77eebf810831 {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) (n : ℕ)
    (z : (tateComplex S.X₃).cycles n) :
    (tateIsoH S.X₁ (n + 1) (n + 1) (Nat.cast_succ n).symm).hom.hom
      ((tδ hS n (n + 1) rfl).hom (((tateComplex S.X₃).homologyπ n).hom z)) =
      δ hS n (n + 1) rfl (π S.X₃ n (cocyclesMk (((tateComplex S.X₃).iCycles n).hom z)
        (tate_d_iCycles _ n z))) := by sorry

alias «GroundTheory».«GroupCoh».«tateIsoH_tδ_homologyπ» := P2M_GroundTheory_GroupCoh_tateIsoH_t__homology__77eebf810831
