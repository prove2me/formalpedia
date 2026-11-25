-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_InflationIsomorphism_pLin_eq_zero
-- name    : ReciprocityTheory.Coh.InflationIsomorphism.pLin_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:50:33.421688+00:00
-- url     : https://prove2.me/theorems/b7cbe808-207e-50f8-86ab-f85ce67e2439
-- title:
--   Inflation Isomorphism: p Lin eq zero
-- statement:
--   The Inflation Isomorphism construction uses the p Lin eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfIsoA.lean#L163-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfIsoA.lean#L163-L164

import Definitions.Def_ReciprocityTheory_GroupCohomology_CardLenStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfIsoA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function Topology
noncomputable section
universe u
open ReciprocityTheory.Coh.InflationIsomorphism
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

theorem ReciprocityTheory.Coh.InflationIsomorphism.pLin_eq_zero (M : TRep R G) (c : (CG M).V) : pLin M c = 0 ↔ c ∈ LinearMap.range (iCG M) := by sorry
