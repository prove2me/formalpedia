-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_inv
-- name    : ReciprocityTheory.ChartRestriction.G.SA.good_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:17.895166+00:00
-- url     : https://prove2.me/theorems/775ad183-a367-4125-8cc0-715c721f01c7
-- title:
--   SA: good inv
-- statement:
--   The SA construction uses the good inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ConjMemEichSet.lean#L109-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ConjMemEichSet.lean#L109-L120

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
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
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef

theorem ReciprocityTheory.ChartRestriction.G.SA.good_inv {g : Matrix ι ι K} (hg : g ∈ Good σ J e f) :
    ∃ g' ∈ Good σ J e f, g' * g = 1 ∧ g * g' = 1 := by sorry
