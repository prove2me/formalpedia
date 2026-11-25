-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__mk_rep_1c035d958e91
-- name    : P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__mk_rep_1c035d958e91
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:43.446276+00:00
-- url     : https://prove2.me/theorems/8334d766-e94e-4c2f-93b8-4c90e2ba86f1
-- title:
--   P2 M Reciprocity Theory Coh Cohomology Functoriality  mk rep 1c035d958e91: P2 M Reciprocity Theory Coh Cohomology Functoriality  mk rep 1c035d958e91
-- statement:
--   The P2 M Reciprocity Theory Coh Cohomology Functoriality  mk rep 1c035d958e91 construction uses the P2 M Reciprocity Theory Coh Cohomology Functoriality  mk rep 1c035d958e91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L77-L79

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

theorem P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__mk_rep_1c035d958e91 (g : G) : (Quotient.mk (QuotientGroup.rightRel U) (rep U g)) = Quotient.mk _ g := by sorry

alias «ReciprocityTheory».«Coh».«CohomologyFunctoriality₂».«mk_rep» := P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__mk_rep_1c035d958e91
