-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_cycR_sub_vertR_ca3c50543c93
-- name    : P2M_GroundTheory_Heights__Heights_Inter_cycR_sub_vertR_ca3c50543c93
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:38.728969+00:00
-- url     : https://prove2.me/theorems/2ea80e31-a12e-4765-86e8-ebd20e8a99a3
-- title:
--   P2 M Ground Theory Heights  Heights Inter cyc R sub vert R ca3c50543c93: P2 M Ground Theory Heights  Heights Inter cyc R sub vert R ca3c50543c93
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter cyc R sub vert R ca3c50543c93 construction uses the P2 M Ground Theory Heights  Heights Inter cyc R sub vert R ca3c50543c93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PConsequences.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PConsequences.lean#L36-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDerived
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ConservationDegreeFormOfExistence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PConsequences
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_cycR_sub_vertR_ca3c50543c93 (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) [DecidablePred (IsHorizontal (ι := ι))] :
    cycR I P L s - vertR P L s = ∑ W ∈ (divSupp_finite P s).toFinset.filter IsHorizontal,
      (multAt (P ⊔ Ideal.span {s}) W : ℝ) * I W n L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«cycR_sub_vertR» := P2M_GroundTheory_Heights__Heights_Inter_cycR_sub_vertR_ca3c50543c93
