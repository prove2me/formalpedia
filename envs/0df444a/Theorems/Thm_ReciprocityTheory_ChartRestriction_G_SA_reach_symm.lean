-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reach_symm
-- name    : ReciprocityTheory.ChartRestriction.G.SA.reach_symm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:35:16.446901+00:00
-- url     : https://prove2.me/theorems/e694c841-f678-45f9-92c7-db82ac225072
-- title:
--   SA: reach symm
-- statement:
--   The SA construction uses the reach symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ReachableFixingAddSmulSecond.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ReachableFixingAddSmulSecond.lean#L35-L42

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

theorem ReciprocityTheory.ChartRestriction.G.SA.reach_symm {b b' : ι → K} (h : Reach σ J e f a b b') : Reach σ J e f a b' b := by sorry
