-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_nsmul_8dc4b1f20659
-- name    : P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_nsmul_8dc4b1f20659
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:17:21.76581+00:00
-- url     : https://prove2.me/theorems/099fccf8-02f5-5eed-8a6c-ad0035ef8a85
-- title:
--   P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H nsmul 8dc4b1f20659: P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H nsmul 8dc4b1f20659
-- statement:
--   The P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H nsmul 8dc4b1f20659 construction uses the P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H nsmul 8dc4b1f20659 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L38-L44

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

theorem P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_nsmul_8dc4b1f20659 (φ : Hom A A) (k : ℕ) (n : ℕ) (h : ∀ x, φ.f n x = k • x) (y : A.H n) :
    φ.H n y = k • y := by sorry

alias «ReciprocityTheory».«Coh».«CohomologyFunctoriality₂».«Hom».«H_nsmul» := P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_nsmul_8dc4b1f20659
