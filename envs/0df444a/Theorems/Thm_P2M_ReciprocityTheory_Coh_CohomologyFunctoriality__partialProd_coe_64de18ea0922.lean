-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__partialProd_coe_64de18ea0922
-- name    : P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__partialProd_coe_64de18ea0922
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:17:50.454565+00:00
-- url     : https://prove2.me/theorems/c9f28e1a-c71c-4d8c-bd69-039c4756c6d9
-- title:
--   P2 M Reciprocity Theory Coh Cohomology Functoriality  partial Prod coe 64de18ea0922: P2 M Reciprocity Theory Coh Cohomology Functoriality  partial Prod coe 64de18ea0922
-- statement:
--   The P2 M Reciprocity Theory Coh Cohomology Functoriality  partial Prod coe 64de18ea0922 construction uses the P2 M Reciprocity Theory Coh Cohomology Functoriality  partial Prod coe 64de18ea0922 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L301-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L301-L305

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

theorem P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__partialProd_coe_64de18ea0922 {N : Subgroup G} {n : ℕ} (g : Fin n → N) (j : Fin (n + 1)) :
    Fin.partialProd (fun i => (g i : G)) j = ((Fin.partialProd g j : N) : G) := by sorry

alias «ReciprocityTheory».«Coh».«CohomologyFunctoriality₂».«partialProd_coe» := P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__partialProd_coe_64de18ea0922
