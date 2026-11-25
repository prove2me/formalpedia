-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh___cyclesMap_revHom_bb8ed231e974
-- name    : P2M_GroundTheory_GroupCoh___cyclesMap_revHom_bb8ed231e974
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:47.326799+00:00
-- url     : https://prove2.me/theorems/887ee3aa-353f-4106-96d6-847cadba1be0
-- title:
--   P2 M Ground Theory Group Coh   cycles Map rev Hom bb8ed231e974: P2 M Ground Theory Group Coh   cycles Map rev Hom bb8ed231e974
-- statement:
--   The P2 M Ground Theory Group Coh   cycles Map rev Hom bb8ed231e974 construction uses the P2 M Ground Theory Group Coh   cycles Map rev Hom bb8ed231e974 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CochainReverse.lean#L251-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CochainReverse.lean#L251-L255

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_CochainReverse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory Limits groupCohomology
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A : Rep k G} {n : ℕ}

theorem P2M_GroundTheory_GroupCoh___cyclesMap_revHom_bb8ed231e974 (z : cocycles A n) :
    π A n (HomologicalComplex.cyclesMap (revHom A) n z) = π A n z := by sorry

alias «GroundTheory».«GroupCoh».«π_cyclesMap_revHom» := P2M_GroundTheory_GroupCoh___cyclesMap_revHom_bb8ed231e974
