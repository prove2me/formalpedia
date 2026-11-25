-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_map_H1__augCocycle_051c44b13fd0
-- name    : P2M_GroundTheory_GroupCoh_map_H1__augCocycle_051c44b13fd0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:19:03.161516+00:00
-- url     : https://prove2.me/theorems/59eef564-c2bd-59f9-8f53-01caa830a9e6
-- title:
--   P2 M Ground Theory Group Coh map H1  aug Cocycle 051c44b13fd0: P2 M Ground Theory Group Coh map H1  aug Cocycle 051c44b13fd0
-- statement:
--   The P2 M Ground Theory Group Coh map H1  aug Cocycle 051c44b13fd0 construction uses the P2 M Ground Theory Group Coh map H1  aug Cocycle 051c44b13fd0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingModule.lean#L48-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingModule.lean#L48-L57

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
omit [Fintype G]

theorem P2M_GroundTheory_GroupCoh_map_H1__augCocycle_051c44b13fd0 {H : Type u} [Group H] (φ : H →* G) {A : Rep.{u} k G}
    (f : cocycles₁ A) :
    map (A := res φ (augIdeal k G)) (B := res φ A) (MonoidHom.id H)
      ((resFunctor φ).map (cocycleHom f)) 1 (H1π _ (augCocycle k φ)) =
    map φ (𝟙 (res φ A)) 1 (H1π A f) := by sorry

alias «GroundTheory».«GroupCoh».«map_H1π_augCocycle» := P2M_GroundTheory_GroupCoh_map_H1__augCocycle_051c44b13fd0
