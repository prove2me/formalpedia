-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_sum_2c8caae4364b
-- name    : P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_sum_2c8caae4364b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:17:21.105694+00:00
-- url     : https://prove2.me/theorems/ad476d43-168a-514b-ba58-29bb30c126a6
-- title:
--   P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H sum 2c8caae4364b: P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H sum 2c8caae4364b
-- statement:
--   The P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H sum 2c8caae4364b construction uses the P2 M Reciprocity Theory Coh Cohomology Functoriality  Hom H sum 2c8caae4364b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L46-L56

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

theorem P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_sum_2c8caae4364b {ι : Type*} (s : Finset ι) (φ : Hom A B) (ψ : ι → Hom A B) (n : ℕ)
    (h : ∀ x, φ.f n x = ∑ c ∈ s, (ψ c).f n x) (y : A.H n) :
    φ.H n y = ∑ c ∈ s, (ψ c).H n y := by sorry

alias «ReciprocityTheory».«Coh».«CohomologyFunctoriality₂».«Hom».«H_sum» := P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_sum_2c8caae4364b
