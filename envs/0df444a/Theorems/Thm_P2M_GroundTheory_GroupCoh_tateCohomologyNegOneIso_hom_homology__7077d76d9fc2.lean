-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateCohomologyNegOneIso_hom_homology__7077d76d9fc2
-- name    : P2M_GroundTheory_GroupCoh_tateCohomologyNegOneIso_hom_homology__7077d76d9fc2
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:08:05.992671+00:00
-- url     : https://prove2.me/theorems/e11091ca-7f34-5158-ab8b-6609732e91e5
-- title:
--   P2 M Ground Theory Group Coh tate Cohomology Neg One Iso hom homology  7077d76d9fc2: P2 M Ground Theory Group Coh tate Cohomology Neg One Iso hom homology  7077d76d9fc2
-- statement:
--   The P2 M Ground Theory Group Coh tate Cohomology Neg One Iso hom homology  7077d76d9fc2 construction uses the P2 M Ground Theory Group Coh tate Cohomology Neg One Iso hom homology  7077d76d9fc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateLow.lean#L345-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateLow.lean#L345-L352

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

theorem P2M_GroundTheory_GroupCoh_tateCohomologyNegOneIso_hom_homology__7077d76d9fc2 (M : Rep.{u} R G) (z : (tateComplex M).cycles (-1))
    (x : LinearMap.ker M.ρ.norm)
    (hx : (chainsIso₀ M).inv.hom x = ((tateComplex M).iCycles (-1)).hom z) :
    ((tateCohomologyNegOneIso R G).app M).hom.hom (((tateComplex M).homologyπ (-1)).hom z) =
      Submodule.Quotient.mk x := by sorry

alias «GroundTheory».«GroupCoh».«tateCohomologyNegOneIso_hom_homologyπ» := P2M_GroundTheory_GroupCoh_tateCohomologyNegOneIso_hom_homology__7077d76d9fc2
