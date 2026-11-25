-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_inf_res_exact
-- name    : ReciprocityTheory.Coh.InflationRestrictionInvariants.inf_res_exact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:50:04.566416+00:00
-- url     : https://prove2.me/theorems/c2fd8929-1b6c-42f0-ab37-a2dee0104be7
-- title:
--   Inflation Restriction Invariants: inf res exact
-- statement:
--   The Inflation Restriction Invariants construction uses the inf res exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfRes.lean#L167-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfRes.lean#L167-L237

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants
open ReciprocityTheory.Gal Cx Function
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.Coh.InflationRestrictionInvariants.inf_res_exact (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)
    (hP : IsInvRep M N Q P) :
    Exact (P.hom.H 1) ((Pair.res M N.subtype continuous_subtype_val).hom.H 1) := by sorry
