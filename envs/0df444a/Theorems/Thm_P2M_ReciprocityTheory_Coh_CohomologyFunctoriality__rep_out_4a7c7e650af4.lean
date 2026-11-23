-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__rep_out_4a7c7e650af4
-- name    : P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__rep_out_4a7c7e650af4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:23.300311+00:00
-- url     : https://prove2.me/theorems/3f0ffebe-5684-4ed5-92bd-4ff07f7f5b1b
-- title:
--   P2 M Reciprocity Theory Coh Cohomology Functoriality  rep out 4a7c7e650af4: P2 M Reciprocity Theory Coh Cohomology Functoriality  rep out 4a7c7e650af4
-- statement:
--   The P2 M Reciprocity Theory Coh Cohomology Functoriality  rep out 4a7c7e650af4 construction uses the P2 M Reciprocity Theory Coh Cohomology Functoriality  rep out 4a7c7e650af4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L73-L75

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

theorem P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__rep_out_4a7c7e650af4 (c : Quotient (QuotientGroup.rightRel U)) : rep U c.out = c.out := by sorry

alias «ReciprocityTheory».«Coh».«CohomologyFunctoriality₂».«rep_out» := P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__rep_out_4a7c7e650af4
