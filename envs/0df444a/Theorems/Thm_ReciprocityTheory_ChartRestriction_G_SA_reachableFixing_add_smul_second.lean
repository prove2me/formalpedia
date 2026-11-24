-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reachableFixing_add_smul_second
-- name    : ReciprocityTheory.ChartRestriction.G.SA.reachableFixing_add_smul_second
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:46.896798+00:00
-- url     : https://prove2.me/theorems/5e4467f0-6a7d-4a98-a6df-82218186a03b
-- title:
--   SA: reachable Fixing add smul second
-- statement:
--   The SA construction uses the reachable Fixing add smul second property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ReachableFixingAddSmulSecond.lean#L138-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ReachableFixingAddSmulSecond.lean#L138-L160

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

theorem ReciprocityTheory.ChartRestriction.G.SA.reachableFixing_add_smul_second {c : K} (hc : σ c = -c) (b : ι → K) :
    Reach σ J e f a b (b + (c * hf σ J b f) • f) := by sorry
