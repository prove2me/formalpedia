-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_DivisorCycleSwap_not_lt_of_dim_eq
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap.not_lt_of_dim_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:31.108798+00:00
-- url     : https://prove2.me/theorems/42bbd437-40a4-4007-9596-e30c91b6eaa0
-- title:
--   Divisor Cycle Swap: not lt of dim eq
-- statement:
--   The Divisor Cycle Swap construction uses the not lt of dim eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemMinimalPrimesOfMemDivSuppDivSupp.lean#L69-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemMinimalPrimesOfMemDivSuppDivSupp.lean#L69-L88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
open SwapLoc
open ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap.not_lt_of_dim_eq {R : Type*} [CommRing R] {P Q : Ideal R} [hP : P.IsPrime] [Q.IsPrime]
    (hlt : P < Q) {d : ℕ} (hPd : ringKrullDim (R ⧸ P) = (d : WithBot ℕ∞))
    (hQd : ringKrullDim (R ⧸ Q) = (d : WithBot ℕ∞)) : False := by sorry
