-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_cycR_eq_sum_15b112079e4e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_cycR_eq_sum_15b112079e4e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:00.877238+00:00
-- url     : https://prove2.me/theorems/f7e1d180-f3ce-42cd-8f4a-68e150a9fcde
-- title:
--   P2 M Ground Theory Heights  Heights Inter cyc R eq sum 15b112079e4e: P2 M Ground Theory Heights  Heights Inter cyc R eq sum 15b112079e4e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter cyc R eq sum 15b112079e4e construction uses the P2 M Ground Theory Heights  Heights Inter cyc R eq sum 15b112079e4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean#L73-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean#L73-L92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogTwoXc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_cycR_eq_sum_15b112079e4e (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) :
    cycR I P L s = (divCycle P s).sum fun W m => (m : ℝ) * cycWeight I L W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«cycR_eq_sum» := P2M_GroundTheory_Heights__Heights_Inter_cycR_eq_sum_15b112079e4e
