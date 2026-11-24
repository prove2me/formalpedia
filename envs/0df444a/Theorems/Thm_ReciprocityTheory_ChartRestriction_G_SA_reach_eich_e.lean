-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reach_eich_e
-- name    : ReciprocityTheory.ChartRestriction.G.SA.reach_eich_e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:29.801819+00:00
-- url     : https://prove2.me/theorems/9f9f4995-bf14-47d0-b4a1-fd4b601548d2
-- title:
--   SA: reach eich e
-- statement:
--   The SA construction uses the reach eich e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ReachableFixingAddSmulSecond.lean#L46-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ReachableFixingAddSmulSecond.lean#L46-L68

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

theorem ReciprocityTheory.ChartRestriction.G.SA.reach_eich_e {u : ι → K} {c : K} (hue : hf σ J u e = 0) (huf : hf σ J u f = 0)
    (hc : c + σ c + hf σ J u u = 0) (hua : ∀ j, hf σ J u (a j) = 0) (b : ι → K) :
    Reach σ J e f a b (eich σ J e u c *ᵥ b) := by sorry
