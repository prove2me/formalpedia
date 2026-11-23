-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_mk_525460e2150b
-- name    : P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_mk_525460e2150b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:09.022453+00:00
-- url     : https://prove2.me/theorems/ce41bb39-e19f-467d-823b-088d0e745115
-- title:
--   P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H mk 525460e2150b: P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H mk 525460e2150b
-- statement:
--   The P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H mk 525460e2150b construction uses the P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H mk 525460e2150b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L26-L27

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Coh.CohomologyFunctoriality₂
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {A B C : Cx R}

theorem P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_mk_525460e2150b (φ : Hom A B) (n : ℕ) (z : A.Z n) :
    φ.H n (Submodule.Quotient.mk z) = Submodule.Quotient.mk (φ.Z n z) := by sorry

alias «ReciprocityTheory».«Coh».«CohomologyFunctoriality₂».«Hom».«H_mk» := P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_mk_525460e2150b
