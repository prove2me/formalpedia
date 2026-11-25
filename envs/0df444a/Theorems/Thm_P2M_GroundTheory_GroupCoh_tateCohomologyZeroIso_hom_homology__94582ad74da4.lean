-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateCohomologyZeroIso_hom_homology__94582ad74da4
-- name    : P2M_GroundTheory_GroupCoh_tateCohomologyZeroIso_hom_homology__94582ad74da4
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:42.495611+00:00
-- url     : https://prove2.me/theorems/8031aa2e-38d7-4290-b665-9b002f674623
-- title:
--   P2 M Ground Theory Group Coh tate Cohomology Zero Iso hom homology  94582ad74da4: P2 M Ground Theory Group Coh tate Cohomology Zero Iso hom homology  94582ad74da4
-- statement:
--   The P2 M Ground Theory Group Coh tate Cohomology Zero Iso hom homology  94582ad74da4 construction uses the P2 M Ground Theory Group Coh tate Cohomology Zero Iso hom homology  94582ad74da4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateLow.lean#L216-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateLow.lean#L216-L222

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData
import Definitions.Def_GroundTheory_TateCohomology_TateLow
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
open CategoryTheory Limits Representation groupCohomology groupHomology
universe u
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

theorem P2M_GroundTheory_GroupCoh_tateCohomologyZeroIso_hom_homology__94582ad74da4 (M : Rep.{u} R G) (z : (tateComplex M).cycles 0)
    (x : M.ρ.invariants) (hx : (cochainsIso₀ M).inv.hom x = ((tateComplex M).iCycles 0).hom z) :
    ((tateCohomologyZeroIso R G).app M).hom.hom (((tateComplex M).homologyπ 0).hom z) =
      Submodule.Quotient.mk x := by sorry

alias «GroundTheory».«GroupCoh».«tateCohomologyZeroIso_hom_homologyπ» := P2M_GroundTheory_GroupCoh_tateCohomologyZeroIso_hom_homology__94582ad74da4
