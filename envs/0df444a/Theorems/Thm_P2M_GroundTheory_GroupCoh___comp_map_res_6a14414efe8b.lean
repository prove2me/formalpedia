-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh___comp_map_res_6a14414efe8b
-- name    : P2M_GroundTheory_GroupCoh___comp_map_res_6a14414efe8b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:44.748192+00:00
-- url     : https://prove2.me/theorems/8e1e2b32-ccea-4445-afed-637d906733bd
-- title:
--   P2 M Ground Theory Group Coh   comp map res 6a14414efe8b: P2 M Ground Theory Group Coh   comp map res 6a14414efe8b
-- statement:
--   The P2 M Ground Theory Group Coh   comp map res 6a14414efe8b construction uses the P2 M Ground Theory Group Coh   comp map res 6a14414efe8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DeltaMap.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DeltaMap.lean#L34-L38

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

theorem P2M_GroundTheory_GroupCoh___comp_map_res_6a14414efe8b (f : G →* H) {X : ShortComplex (Rep k H)} (hX : X.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f (𝟙 (res f X.X₁)) j =
      map f (𝟙 (res f X.X₃)) i ≫ δ ((shortExact_res f).2 hX) i j hij := by sorry

alias «GroundTheory».«GroupCoh».«δ_comp_map_res» := P2M_GroundTheory_GroupCoh___comp_map_res_6a14414efe8b
