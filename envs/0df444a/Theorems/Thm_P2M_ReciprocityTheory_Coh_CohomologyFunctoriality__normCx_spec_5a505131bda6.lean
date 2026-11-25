-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__normCx_spec_5a505131bda6
-- name    : P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__normCx_spec_5a505131bda6
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:17:27.666987+00:00
-- url     : https://prove2.me/theorems/1885a862-719a-58a7-b694-b7542568cb65
-- title:
--   P2 M Reciprocity Theory Coh Cohomology Functoriality  norm Cx spec 5a505131bda6: P2 M Reciprocity Theory Coh Cohomology Functoriality  norm Cx spec 5a505131bda6
-- statement:
--   The P2 M Reciprocity Theory Coh Cohomology Functoriality  norm Cx spec 5a505131bda6 construction uses the P2 M Reciprocity Theory Coh Cohomology Functoriality  norm Cx spec 5a505131bda6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L240-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L240-L245

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
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : TRep R G) (U : Subgroup G) [U.FiniteIndex]
variable {M U}

theorem P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__normCx_spec_5a505131bda6 (A : Cx R) (eA : ∀ n, A.X n ≃ₗ[R] hcoch (M.resSub U) G n)
    (hA : IsHomog (M.resSub U) G A eA) (eG : ∀ n, M.coch.X n ≃ₗ[R] hcoch M G n) (hG : IsHomog M G M.coch eG)
    (n : ℕ) (F : A.X n) : (eG n ((normCx A eA hA eG hG).f n F)).1 = normF M U n (eA n F).1 := by sorry

alias «ReciprocityTheory».«Coh».«CohomologyFunctoriality₂».«normCx_spec» := P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__normCx_spec_5a505131bda6
