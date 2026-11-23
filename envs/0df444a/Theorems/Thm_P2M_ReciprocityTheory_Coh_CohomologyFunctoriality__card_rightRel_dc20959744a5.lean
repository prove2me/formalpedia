-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__card_rightRel_dc20959744a5
-- name    : P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__card_rightRel_dc20959744a5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:31.79858+00:00
-- url     : https://prove2.me/theorems/ab3f0570-6006-4666-8b70-accb81b7b53b
-- title:
--   P2 M Reciprocity Theory Coh Cohomology Functoriality  card right Rel dc20959744a5: P2 M Reciprocity Theory Coh Cohomology Functoriality  card right Rel dc20959744a5
-- statement:
--   The P2 M Reciprocity Theory Coh Cohomology Functoriality  card right Rel dc20959744a5 construction uses the P2 M Reciprocity Theory Coh Cohomology Functoriality  card right Rel dc20959744a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L107-L110

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

theorem P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__card_rightRel_dc20959744a5 [U.FiniteIndex] [Fintype (Quotient (QuotientGroup.rightRel U))] :
    Fintype.card (Quotient (QuotientGroup.rightRel U)) = U.index := by sorry

alias «ReciprocityTheory».«Coh».«CohomologyFunctoriality₂».«card_rightRel» := P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__card_rightRel_dc20959744a5
