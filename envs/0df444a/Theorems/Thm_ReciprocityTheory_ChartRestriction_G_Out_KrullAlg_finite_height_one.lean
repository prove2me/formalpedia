-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_KrullAlg_finite_height_one
-- name    : ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.finite_height_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:31:16.579364+00:00
-- url     : https://prove2.me/theorems/a6b86e4d-ced8-50cb-b291-c92b7059e225
-- title:
--   Krull Alg: finite height one
-- statement:
--   The Krull Alg construction uses the finite height one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/MemRangeOfForallHeightOne.lean#L148-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/MemRangeOfForallHeightOne.lean#L148-L184

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
omit [IsFractionRing A K]

theorem ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.finite_height_one [IsNoetherianRing A] {a : A} (ha : a ≠ 0) :
    {P : Ideal A | P.IsPrime ∧ P.height = 1 ∧ a ∈ P}.Finite := by sorry
