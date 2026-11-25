-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateZeroClass_eq_homology__afc98be0d3f9
-- name    : P2M_GroundTheory_GroupCoh_tateZeroClass_eq_homology__afc98be0d3f9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:29.471436+00:00
-- url     : https://prove2.me/theorems/642e7805-98b5-46ef-98f4-e5d6e56a5aca
-- title:
--   P2 M Ground Theory Group Coh tate Zero Class eq homology  afc98be0d3f9: P2 M Ground Theory Group Coh tate Zero Class eq homology  afc98be0d3f9
-- statement:
--   The P2 M Ground Theory Group Coh tate Zero Class eq homology  afc98be0d3f9 construction uses the P2 M Ground Theory Group Coh tate Zero Class eq homology  afc98be0d3f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateZeroClass.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateZeroClass.lean#L16-L19

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
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
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem P2M_GroundTheory_GroupCoh_tateZeroClass_eq_homology__afc98be0d3f9 (M : Rep.{u} k G) (z : (tateComplex M).cycles 0)
    (x : M.ρ.invariants) (hx : (cochainsIso₀ M).inv.hom x = ((tateComplex M).iCycles 0).hom z) :
    tateZeroClass M x = ((tateComplex M).homologyπ 0).hom z := by sorry

alias «GroundTheory».«GroupCoh».«tateZeroClass_eq_homologyπ» := P2M_GroundTheory_GroupCoh_tateZeroClass_eq_homology__afc98be0d3f9
