-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_inflD_mul_right
-- name    : ReciprocityTheory.Coh.InflationTransgression.inflD_mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:35.251801+00:00
-- url     : https://prove2.me/theorems/4d719b4f-7620-4fa6-aed8-6bcab6631b25
-- title:
--   Inflation Transgression: infl D mul right
-- statement:
--   The Inflation Transgression construction uses the infl D mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/TransgressionA.lean#L203-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/TransgressionA.lean#L203-L206

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
variable (M : TRep R G) (N : Subgroup G) [N.Normal] (y : G → M.V) (hy1 : y 1 = 0)
  (hD : InflD M N (D1 M y))
include hy1 hD

theorem ReciprocityTheory.Coh.InflationTransgression.inflD_mul_right (a : G) (n : N) : y (a * n) = y a + M.rho a (y n) := by sorry
