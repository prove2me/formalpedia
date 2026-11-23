-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh___comp_map_002a70015e3d
-- name    : P2M_GroundTheory_GroupCoh___comp_map_002a70015e3d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:05.871618+00:00
-- url     : https://prove2.me/theorems/0e8b8b14-964d-4400-a5ae-0c77f1e16a79
-- title:
--   P2 M Ground Theory Group Coh   comp map 002a70015e3d: P2 M Ground Theory Group Coh   comp map 002a70015e3d
-- statement:
--   The P2 M Ground Theory Group Coh   comp map 002a70015e3d construction uses the P2 M Ground Theory Group Coh   comp map 002a70015e3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DeltaMap.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DeltaMap.lean#L27-L32

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
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
open CategoryTheory groupCohomology Rep
universe u
variable {k G H : Type u} [CommRing k] [Group G] [Group H]

theorem P2M_GroundTheory_GroupCoh___comp_map_002a70015e3d (f : G →* H) {X : ShortComplex (Rep k H)} {Y : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (hY : Y.ShortExact) (F : X.map (resFunctor f) ⟶ Y)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f F.τ₁ j = map f F.τ₃ i ≫ δ hY i j hij := by sorry

alias «GroundTheory».«GroupCoh».«δ_comp_map» := P2M_GroundTheory_GroupCoh___comp_map_002a70015e3d
