-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_comp_0576ef890fe4
-- name    : P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_comp_0576ef890fe4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:31.854048+00:00
-- url     : https://prove2.me/theorems/64ec0d93-0482-4d3e-9542-651dd216f136
-- title:
--   P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H comp 0576ef890fe4: P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H comp 0576ef890fe4
-- statement:
--   The P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H comp 0576ef890fe4 construction uses the P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H comp 0576ef890fe4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L29-L32

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

theorem P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_comp_0576ef890fe4 (φ : Hom A B) (ψ : Hom B C) (n : ℕ) (y : A.H n) :
    (ψ.comp φ).H n y = ψ.H n (φ.H n y) := by sorry

alias «ReciprocityTheory».«Coh».«CohomologyFunctoriality₂».«Hom».«H_comp» := P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_comp_0576ef890fe4
