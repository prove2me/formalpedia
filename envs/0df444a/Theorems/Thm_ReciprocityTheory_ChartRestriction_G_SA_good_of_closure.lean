-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_good_of_closure
-- name    : ReciprocityTheory.ChartRestriction.G.SA.good_of_closure
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:26.301704+00:00
-- url     : https://prove2.me/theorems/698fac5b-c353-4df3-a3bb-bd5520ed5a44
-- title:
--   SA: good of closure
-- statement:
--   The SA construction uses the good of closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ConjMemEichSet.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ConjMemEichSet.lean#L92-L94

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

theorem ReciprocityTheory.ChartRestriction.G.SA.good_of_closure {n : Matrix ι ι K} (hn : n ∈ Submonoid.closure (eichSet σ J e f)) :
    n ∈ Good σ J e f := by sorry
