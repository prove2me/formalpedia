-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_normSegre_sameOrbit_b77e8e882eac
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_normSegre_sameOrbit_b77e8e882eac
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:00:53.898311+00:00
-- url     : https://prove2.me/theorems/b7cd236f-0130-449c-baa9-db92df513409
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pullback Degree Count norm Segre same Orbit b77e8e882eac: P2 M Ground Theory Heights  Heights Inter Pullback Degree Count norm Segre same Orbit b77e8e882eac
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pullback Degree Count norm Segre same Orbit b77e8e882eac construction uses the P2 M Ground Theory Heights  Heights Inter Pullback Degree Count norm Segre same Orbit b77e8e882eac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NormSegreSameOrbit.lean#L44-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NormSegreSameOrbit.lean#L44-L55

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOver
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NormSegreSameOrbit
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_normSegre_sameOrbit_b77e8e882eac {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) {n : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {z₁ z₂ : (Σ k', ι' k') → ℂ} (h : SameOrbit z₁ z₂) :
    (Ψ (segre fun p => z₁ (v p)) 0)⁻¹ • segre (fun p => z₁ (v p)) =
      (Ψ (segre fun p => z₂ (v p)) 0)⁻¹ • segre (fun p => z₂ (v p)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PullbackDegreeCount».«normSegre_sameOrbit» := P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_normSegre_sameOrbit_b77e8e882eac
