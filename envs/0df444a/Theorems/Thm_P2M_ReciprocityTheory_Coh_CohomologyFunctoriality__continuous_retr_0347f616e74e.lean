-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__continuous_retr_0347f616e74e
-- name    : P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__continuous_retr_0347f616e74e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:44.592699+00:00
-- url     : https://prove2.me/theorems/f4484129-232a-44c0-869c-ddc744baa458
-- title:
--   P2 M Reciprocity Theory Coh Cohomology Functoriality  continuous retr 0347f616e74e: P2 M Reciprocity Theory Coh Cohomology Functoriality  continuous retr 0347f616e74e
-- statement:
--   The P2 M Reciprocity Theory Coh Cohomology Functoriality  continuous retr 0347f616e74e construction uses the P2 M Reciprocity Theory Coh Cohomology Functoriality  continuous retr 0347f616e74e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L101-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L101-L102

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

theorem P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__continuous_retr_0347f616e74e (hU : IsOpen (U : Set G)) : Continuous (retr U) := by sorry

alias «ReciprocityTheory».«Coh».«CohomologyFunctoriality₂».«continuous_retr» := P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__continuous_retr_0347f616e74e
