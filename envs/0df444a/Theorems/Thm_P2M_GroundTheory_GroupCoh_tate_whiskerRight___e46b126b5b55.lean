-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tate_whiskerRight___e46b126b5b55
-- name    : P2M_GroundTheory_GroupCoh_tate_whiskerRight___e46b126b5b55
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:17:08.484676+00:00
-- url     : https://prove2.me/theorems/6a51426e-c850-5964-9100-eeb7f4d30b44
-- title:
--   P2 M Ground Theory Group Coh tate whisker Right   e46b126b5b55: P2 M Ground Theory Group Coh tate whisker Right   e46b126b5b55
-- statement:
--   The P2 M Ground Theory Group Coh tate whisker Right   e46b126b5b55 construction uses the P2 M Ground Theory Group Coh tate whisker Right   e46b126b5b55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L17-L23

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]

theorem P2M_GroundTheory_GroupCoh_tate_whiskerRight___e46b126b5b55 {H : Type u} [Group H] [Fintype H] {F F' : Rep.{u} k G ⥤ Rep.{u} k H}
    [F.PreservesZeroMorphisms] [F'.PreservesZeroMorphisms] (σ : F ⟶ F')
    {X : ShortComplex (Rep.{u} k G)} (hX : (X.map F).ShortExact) (hX' : (X.map F').ShortExact)
    (n : ℤ) :
    TateCohomology.δ hX n ≫ (tateCohomologyFunctor (n + 1)).map (σ.app X.X₁) =
      (tateCohomologyFunctor n).map (σ.app X.X₃) ≫ TateCohomology.δ hX' n := by sorry

alias «GroundTheory».«GroupCoh».«tate_whiskerRight_δ» := P2M_GroundTheory_GroupCoh_tate_whiskerRight___e46b126b5b55
