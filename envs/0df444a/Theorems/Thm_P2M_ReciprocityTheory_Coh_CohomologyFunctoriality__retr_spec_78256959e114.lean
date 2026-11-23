-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_spec_78256959e114
-- name    : P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_spec_78256959e114
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:06.54949+00:00
-- url     : https://prove2.me/theorems/6e8f771d-fcc2-4ec7-86e4-dd73b438c891
-- title:
--   P2 M Reciprocity Theory Coh Cohomology Functoriality  retr spec 78256959e114: P2 M Reciprocity Theory Coh Cohomology Functoriality  retr spec 78256959e114
-- statement:
--   The P2 M Reciprocity Theory Coh Cohomology Functoriality  retr spec 78256959e114 construction uses the P2 M Reciprocity Theory Coh Cohomology Functoriality  retr spec 78256959e114 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L89-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L89-L89

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
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)

theorem P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_spec_78256959e114 (g : G) : (retr U g : G) = g * (rep U g)⁻¹ := by sorry

alias «ReciprocityTheory».«Coh».«CohomologyFunctoriality₂».«retr_spec» := P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_spec_78256959e114
