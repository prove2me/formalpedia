-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_isOpen_setOf_conj_eq
-- name    : ReciprocityTheory.Coh.InflationTransgression.isOpen_setOf_conj_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:51:46.761799+00:00
-- url     : https://prove2.me/theorems/b216acc1-b3e4-4b49-8bda-75e2889d99a4
-- title:
--   Inflation Transgression: is Open set Of conj eq
-- statement:
--   The Inflation Transgression construction uses the is Open set Of conj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/TransgressionA.lean#L65-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/TransgressionA.lean#L65-L88

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

theorem ReciprocityTheory.Coh.InflationTransgression.isOpen_setOf_conj_eq (M : TRep R G) [DiscreteTopology M.V] (N : Subgroup G) [N.Normal]
    (hNc : IsClosed (N : Set G)) [CompactSpace G] (f : N → M.V) (hf : Continuous f) (m : M.V) :
    IsOpen {s : G | ∀ n : N, M.rho s (f (cj N s n)) - f n = M.rho n m - m} := by sorry
