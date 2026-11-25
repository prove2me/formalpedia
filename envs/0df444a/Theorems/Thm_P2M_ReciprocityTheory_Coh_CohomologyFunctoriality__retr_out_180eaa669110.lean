-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_out_180eaa669110
-- name    : P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_out_180eaa669110
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:17:26.936444+00:00
-- url     : https://prove2.me/theorems/d6db7ff3-3394-50f5-ac13-a49ffbb168fc
-- title:
--   P2 M Reciprocity Theory Coh Cohomology Functoriality  retr out 180eaa669110: P2 M Reciprocity Theory Coh Cohomology Functoriality  retr out 180eaa669110
-- statement:
--   The P2 M Reciprocity Theory Coh Cohomology Functoriality  retr out 180eaa669110 construction uses the P2 M Reciprocity Theory Coh Cohomology Functoriality  retr out 180eaa669110 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L85-L87

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

theorem P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_out_180eaa669110 (c : Quotient (QuotientGroup.rightRel U)) : retr U c.out = 1 := by sorry

alias «ReciprocityTheory».«Coh».«CohomologyFunctoriality₂».«retr_out» := P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_out_180eaa669110
