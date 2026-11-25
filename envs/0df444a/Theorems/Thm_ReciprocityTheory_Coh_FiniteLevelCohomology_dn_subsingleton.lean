-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_FiniteLevelCohomology_dn_subsingleton
-- name    : ReciprocityTheory.Coh.FiniteLevelCohomology.dn_subsingleton
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:21.104204+00:00
-- url     : https://prove2.me/theorems/d26c1056-31a7-5fa7-984b-c8fca7999e28
-- title:
--   Finite Level Cohomology: dn subsingleton
-- statement:
--   The Finite Level Cohomology construction uses the dn subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FiniteLevel.lean#L133-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/FiniteLevel.lean#L133-L142

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Topology
open scoped Pointwise
universe u
open ReciprocityTheory.Coh.FiniteLevelCohomology
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.Coh.FiniteLevelCohomology.dn_subsingleton {K : Type u} [Group K] [TopologicalSpace K] [Subsingleton K]
    (M : TRep R K) (k : ℕ) (f : (Fin k → K) → M.V) (g : Fin (k + 1) → K) :
    dn M.rho k f g = (if Even k then (0 : R) else 1) • f (fun _ => 1) := by sorry
