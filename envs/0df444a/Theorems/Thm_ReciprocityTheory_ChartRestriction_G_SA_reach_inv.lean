-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reach_inv
-- name    : ReciprocityTheory.ChartRestriction.G.SA.reach_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:57.160087+00:00
-- url     : https://prove2.me/theorems/9ffce11b-0d58-4d5e-b27c-d254041c1b22
-- title:
--   SA: reach inv
-- statement:
--   The SA construction uses the reach inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ReachableFixingAddSmulSecond.lean#L183-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ReachableFixingAddSmulSecond.lean#L183-L187

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ReachableFixingAddSmulSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1) {s : ℕ} {a : Fin s → ι → K}
  (hae : ∀ j, hf σ J (a j) e = 0) (haf : ∀ j, hf σ J (a j) f = 0)
include hσ hJ he hff hef
include hae haf

theorem ReciprocityTheory.ChartRestriction.G.SA.reach_inv {b b' : ι → K} (h : Reach σ J e f a b b') (hb : ∀ j, hf σ J b (a j) = 0) :
    (∀ j, hf σ J b' (a j) = 0) ∧ hf σ J b' b' = hf σ J b b := by sorry
