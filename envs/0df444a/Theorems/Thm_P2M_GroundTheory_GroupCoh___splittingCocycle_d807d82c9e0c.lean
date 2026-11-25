-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh___splittingCocycle_d807d82c9e0c
-- name    : P2M_GroundTheory_GroupCoh___splittingCocycle_d807d82c9e0c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:20:04.563404+00:00
-- url     : https://prove2.me/theorems/54e500dd-7474-4662-a8bd-5ef0f180bf66
-- title:
--   P2 M Ground Theory Group Coh   splitting Cocycle d807d82c9e0c: P2 M Ground Theory Group Coh   splitting Cocycle d807d82c9e0c
-- statement:
--   The P2 M Ground Theory Group Coh   splitting Cocycle d807d82c9e0c construction uses the P2 M Ground Theory Group Coh   splitting Cocycle d807d82c9e0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingModule.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingModule.lean#L34-L36

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PullbackExtension
import Definitions.Def_GroundTheory_TateCohomology_AugTrivial
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory Limits groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (M : Rep.{u} k G)
  (u : groupCohomology M 2)

theorem P2M_GroundTheory_GroupCoh___splittingCocycle_d807d82c9e0c :
    δ (coindSES_shortExact M) 1 2 rfl (H1π _ (splittingCocycle M u)) = u := by sorry

alias «GroundTheory».«GroupCoh».«δ_splittingCocycle» := P2M_GroundTheory_GroupCoh___splittingCocycle_d807d82c9e0c
