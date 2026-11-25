-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_KrullAlg_exists_assoc
-- name    : ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.exists_assoc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:31:20.735019+00:00
-- url     : https://prove2.me/theorems/7ef945be-a3d4-4a50-87b1-f10391def295
-- title:
--   Krull Alg: exists assoc
-- statement:
--   The Krull Alg construction uses the exists assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/MemRangeOfForallHeightOne.lean#L31-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/MemRangeOfForallHeightOne.lean#L31-L60

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

theorem ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.exists_assoc [IsNoetherianRing A] {ι : Type*} (x : ι → K)
    (hx : ∃ i, x i ∉ (algebraMap A K).range) :
    ∃ (d : A) (P : Ideal A), P.IsPrime ∧
      (∀ r, r ∈ P ↔ ∀ i, algebraMap A K r * (algebraMap A K d * x i) ∈ (algebraMap A K).range) ∧
      ∃ i, algebraMap A K d * x i ∉ (algebraMap A K).range := by sorry
