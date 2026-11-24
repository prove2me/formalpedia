-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_cycR_eq_vertR_of_dimOne_68048616a4d8
-- name    : P2M_GroundTheory_Heights__Heights_Inter_cycR_eq_vertR_of_dimOne_68048616a4d8
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:42.538535+00:00
-- url     : https://prove2.me/theorems/832989b2-6840-43e6-8162-cce4791064bc
-- title:
--   P2 M Ground Theory Heights  Heights Inter cyc R eq vert R of dim One 68048616a4d8: P2 M Ground Theory Heights  Heights Inter cyc R eq vert R of dim One 68048616a4d8
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter cyc R eq vert R of dim One 68048616a4d8 construction uses the P2 M Ground Theory Heights  Heights Inter cyc R eq vert R of dim One 68048616a4d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean#L197-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalOfDimOne.lean#L197-L202

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

theorem P2M_GroundTheory_Heights__Heights_Inter_cycR_eq_vertR_of_dimOne_68048616a4d8 (h0 : ArithVarZeroStatement) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    {P : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι} (hP : IsArithVar P 1) (hs : IsSectionOn P A s) :
    cycR I P (Fin.elim0 : Fin 0 → HermLine ι) s = vertR P (Fin.elim0 : Fin 0 → HermLine ι) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«cycR_eq_vertR_of_dimOne» := P2M_GroundTheory_Heights__Heights_Inter_cycR_eq_vertR_of_dimOne_68048616a4d8
