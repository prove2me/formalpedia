-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_KrullAlg_mem_range_of_forall_height_one
-- name    : ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:31:33.397211+00:00
-- url     : https://prove2.me/theorems/512ccf21-ebb0-48e5-b54c-84b359937106
-- title:
--   Krull Alg: mem range of forall height one
-- statement:
--   The Krull Alg construction uses the mem range of forall height one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/MemRangeOfForallHeightOne.lean#L137-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/MemRangeOfForallHeightOne.lean#L137-L144

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.Integer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_MemRangeOfForallHeightOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]

theorem ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one [IsNoetherianRing A] [IsIntegrallyClosed A] (x : K)
    (h : ∀ P : Ideal A, P.IsPrime → P.height = 1 →
      ∃ s ∉ P, algebraMap A K s * x ∈ (algebraMap A K).range) :
    x ∈ (algebraMap A K).range := by sorry
