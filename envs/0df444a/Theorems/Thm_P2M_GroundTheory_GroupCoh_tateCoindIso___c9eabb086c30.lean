-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateCoindIso___c9eabb086c30
-- name    : P2M_GroundTheory_GroupCoh_tateCoindIso___c9eabb086c30
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:31:03.047142+00:00
-- url     : https://prove2.me/theorems/a84b7c8a-51b2-5993-819c-2bc02d45c175
-- title:
--   P2 M Ground Theory Group Coh tate Coind Iso   c9eabb086c30: P2 M Ground Theory Group Coh tate Coind Iso   c9eabb086c30
-- statement:
--   The P2 M Ground Theory Group Coh tate Coind Iso   c9eabb086c30 construction uses the P2 M Ground Theory Group Coh tate Coind Iso   c9eabb086c30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateShapiro.lean#L393-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateShapiro.lean#L393-L405

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

theorem P2M_GroundTheory_GroupCoh_tateCoindIso___c9eabb086c30 {X : ShortComplex (Rep.{u} k S)} (hX : X.ShortExact) (n : ℤ) :
    TateCohomology.δ (shortExact_map_coindFunctor S hX) n ≫ (tateCoindIso S X.X₁ (n + 1)).hom =
      (tateCoindIso S X.X₃ n).hom ≫ TateCohomology.δ hX n := by sorry

alias «GroundTheory».«GroupCoh».«tateCoindIso_δ» := P2M_GroundTheory_GroupCoh_tateCoindIso___c9eabb086c30
