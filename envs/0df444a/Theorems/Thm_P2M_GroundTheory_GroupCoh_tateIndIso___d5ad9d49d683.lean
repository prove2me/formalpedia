-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateIndIso___d5ad9d49d683
-- name    : P2M_GroundTheory_GroupCoh_tateIndIso___d5ad9d49d683
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:39:12.497902+00:00
-- url     : https://prove2.me/theorems/020df37a-0c6d-4209-893a-88abdd155e0c
-- title:
--   P2 M Ground Theory Group Coh tate Ind Iso   d5ad9d49d683: P2 M Ground Theory Group Coh tate Ind Iso   d5ad9d49d683
-- statement:
--   The P2 M Ground Theory Group Coh tate Ind Iso   d5ad9d49d683 construction uses the P2 M Ground Theory Group Coh tate Ind Iso   d5ad9d49d683 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateShapiro.lean#L441-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateShapiro.lean#L441-L452

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DiagonalSuccIsoFreeInvSingle
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateShapiro
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
open CategoryTheory Limits groupCohomology groupHomology Rep HomologicalComplex
universe u
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [Fintype G] [Fintype S]

theorem P2M_GroundTheory_GroupCoh_tateIndIso___d5ad9d49d683 {X : ShortComplex (Rep.{u} k S)} (hX : X.ShortExact) (n : ℤ) :
    TateCohomology.δ (shortExact_map_indFunctor S hX) n ≫ (tateIndIso S X.X₁ (n + 1)).hom =
      (tateIndIso S X.X₃ n).hom ≫ TateCohomology.δ hX n := by sorry

alias «GroundTheory».«GroupCoh».«tateIndIso_δ» := P2M_GroundTheory_GroupCoh_tateIndIso___d5ad9d49d683
