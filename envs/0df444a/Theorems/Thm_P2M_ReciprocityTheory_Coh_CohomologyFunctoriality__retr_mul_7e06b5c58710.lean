-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_mul_7e06b5c58710
-- name    : P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_mul_7e06b5c58710
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:27.830791+00:00
-- url     : https://prove2.me/theorems/6326830b-07e9-4001-a5ec-43f0683c266c
-- title:
--   P2 M Reciprocity Theory Coh Cohomology Functoriality  retr mul 7e06b5c58710: P2 M Reciprocity Theory Coh Cohomology Functoriality  retr mul 7e06b5c58710
-- statement:
--   The P2 M Reciprocity Theory Coh Cohomology Functoriality  retr mul 7e06b5c58710 construction uses the P2 M Reciprocity Theory Coh Cohomology Functoriality  retr mul 7e06b5c58710 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L81-L83

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

theorem P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_mul_7e06b5c58710 (x : U) (g : G) : retr U ((x : G) * g) = x * retr U g := by sorry

alias «ReciprocityTheory».«Coh».«CohomologyFunctoriality₂».«retr_mul» := P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_mul_7e06b5c58710
