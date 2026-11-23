-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_oneDifferential_val
-- name    : ReciprocityTheory.Coh.InflationRestrictionInvariants.oneDifferential_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:50.322893+00:00
-- url     : https://prove2.me/theorems/a94857b0-65ef-49fb-b000-36679c0655cc
-- title:
--   Inflation Restriction Invariants: one Differential val
-- statement:
--   The Inflation Restriction Invariants construction uses the one Differential val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfRes.lean#L79-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfRes.lean#L79-L85

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

theorem ReciprocityTheory.Coh.InflationRestrictionInvariants.oneDifferential_val (M : TRep R G) (x : M.coch.X 1) (a b : G) :
    (M.coch.d 1 x).1 ![a, b] = M.rho a (x.1 (e1 b)) - x.1 (e1 (a * b)) + x.1 (e1 a) := by sorry
