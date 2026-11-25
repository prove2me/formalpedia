-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_cycR_mul_c633929bbe81
-- name    : P2M_GroundTheory_Heights__Heights_Inter_cycR_mul_c633929bbe81
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:48.858802+00:00
-- url     : https://prove2.me/theorems/403b2c26-0eeb-47da-ae9c-459065f7cd8c
-- title:
--   P2 M Ground Theory Heights  Heights Inter cyc R mul c633929bbe81: P2 M Ground Theory Heights  Heights Inter cyc R mul c633929bbe81
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter cyc R mul c633929bbe81 construction uses the P2 M Ground Theory Heights  Heights Inter cyc R mul c633929bbe81 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean#L94-L98

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

theorem P2M_GroundTheory_Heights__Heights_Inter_cycR_mul_c633929bbe81 (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) {P : Ideal (MRing ι)}
    (hP : P.IsPrime) {n : ℕ} (L : Fin n → HermLine ι) {s t : MRing ι} (hs : s ∉ P) (ht : t ∉ P) :
    cycR I P L (s * t) = cycR I P L s + cycR I P L t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«cycR_mul» := P2M_GroundTheory_Heights__Heights_Inter_cycR_mul_c633929bbe81
