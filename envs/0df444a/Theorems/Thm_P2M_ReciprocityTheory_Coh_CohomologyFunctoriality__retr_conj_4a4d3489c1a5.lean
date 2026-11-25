-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_conj_4a4d3489c1a5
-- name    : P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_conj_4a4d3489c1a5
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:17:50.637936+00:00
-- url     : https://prove2.me/theorems/7c7d7ef8-beef-4d41-bfcf-e7e461462997
-- title:
--   P2 M Reciprocity Theory Coh Cohomology Functoriality  retr conj 4a4d3489c1a5: P2 M Reciprocity Theory Coh Cohomology Functoriality  retr conj 4a4d3489c1a5
-- statement:
--   The P2 M Reciprocity Theory Coh Cohomology Functoriality  retr conj 4a4d3489c1a5 construction uses the P2 M Reciprocity Theory Coh Cohomology Functoriality  retr conj 4a4d3489c1a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L307-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L307-L313

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

theorem P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_conj_4a4d3489c1a5 (N : Subgroup G) [N.Normal] (s h : G) (hh : h ∈ N) :
    (retr N (s * h) : G) = s * h * (rep N s)⁻¹ := by sorry

alias «ReciprocityTheory».«Coh».«CohomologyFunctoriality₂».«retr_conj» := P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_conj_4a4d3489c1a5
