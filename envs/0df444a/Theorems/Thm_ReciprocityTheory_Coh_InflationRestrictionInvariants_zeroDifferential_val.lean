-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_zeroDifferential_val
-- name    : ReciprocityTheory.Coh.InflationRestrictionInvariants.zeroDifferential_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:52.766818+00:00
-- url     : https://prove2.me/theorems/f4e2c069-bb48-4e65-8670-46862ee64d26
-- title:
--   Inflation Restriction Invariants: zero Differential val
-- statement:
--   The Inflation Restriction Invariants construction uses the zero Differential val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfRes.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfRes.lean#L107-L110

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

theorem ReciprocityTheory.Coh.InflationRestrictionInvariants.zeroDifferential_val (M : TRep R G) (y : M.coch.X 0) (a : G) :
    (M.coch.d 0 y).1 (e1 a) = M.rho a (y.1 ![]) - y.1 ![] := by sorry
