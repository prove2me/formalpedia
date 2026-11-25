-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_barResolution___f_zero_single_ee18ab47ac91
-- name    : P2M_GroundTheory_GroupCoh_barResolution___f_zero_single_ee18ab47ac91
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:50.887289+00:00
-- url     : https://prove2.me/theorems/9bd0c6c0-cbb6-4441-a1e7-1ca8c9b9714c
-- title:
--   P2 M Ground Theory Group Coh bar Resolution   f zero single ee18ab47ac91: P2 M Ground Theory Group Coh bar Resolution   f zero single ee18ab47ac91
-- statement:
--   The P2 M Ground Theory Group Coh bar Resolution   f zero single ee18ab47ac91 construction uses the P2 M Ground Theory Group Coh bar Resolution   f zero single ee18ab47ac91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DiagonalSuccIsoFreeInvSingle.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DiagonalSuccIsoFreeInvSingle.lean#L83-L88

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DiagonalSuccIsoFreeInvSingle
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
open CategoryTheory Limits groupCohomology Rep
universe v w u
variable {k G : Type u} [CommRing k] [Group G]

theorem P2M_GroundTheory_GroupCoh_barResolution___f_zero_single_ee18ab47ac91 (v : Fin 0 → G) (g : G) (r : k) :
    ((barResolution k G).π.f 0).hom (Finsupp.single v (MonoidAlgebra.single g r)) = r := by sorry

alias «GroundTheory».«GroupCoh».«barResolution_π_f_zero_single» := P2M_GroundTheory_GroupCoh_barResolution___f_zero_single_ee18ab47ac91
