-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_cj_coe
-- name    : ReciprocityTheory.Coh.InflationTransgression.cj_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:32.966817+00:00
-- url     : https://prove2.me/theorems/3b5017f8-6b89-471d-a7cb-831a25595d57
-- title:
--   Inflation Transgression: cj coe
-- statement:
--   The Inflation Transgression construction uses the cj coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/TransgressionA.lean#L63-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/TransgressionA.lean#L63-L63

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_Section
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationTransgression
open ReciprocityTheory.Gal ReciprocityTheory.Coh
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.Coh.InflationTransgression.cj_coe (N : Subgroup G) [N.Normal] (s : G) (n : N) : (cj N s n : G) = s⁻¹ * n * s := by sorry

attribute [defeq] ReciprocityTheory.Coh.InflationTransgression.cj_coe
