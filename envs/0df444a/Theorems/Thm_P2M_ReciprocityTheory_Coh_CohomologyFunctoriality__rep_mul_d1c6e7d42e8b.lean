-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__rep_mul_d1c6e7d42e8b
-- name    : P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__rep_mul_d1c6e7d42e8b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:09:44.068637+00:00
-- url     : https://prove2.me/theorems/4e14484e-f6a8-487d-bc90-818ba3840651
-- title:
--   P2 M Reciprocity Theory Coh Cohomology Functoriality  rep mul d1c6e7d42e8b: P2 M Reciprocity Theory Coh Cohomology Functoriality  rep mul d1c6e7d42e8b
-- statement:
--   The P2 M Reciprocity Theory Coh Cohomology Functoriality  rep mul d1c6e7d42e8b construction uses the P2 M Reciprocity Theory Coh Cohomology Functoriality  rep mul d1c6e7d42e8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PartialProdCoe.lean#L68-L71

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

theorem P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__rep_mul_d1c6e7d42e8b (x : U) (g : G) : rep U ((x : G) * g) = rep U g := by sorry

alias «ReciprocityTheory».«Coh».«CohomologyFunctoriality₂».«rep_mul» := P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__rep_mul_d1c6e7d42e8b
