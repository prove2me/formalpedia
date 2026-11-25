-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_ncard_pullW_eq_558ce03dd39e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_ncard_pullW_eq_558ce03dd39e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:40:45.447245+00:00
-- url     : https://prove2.me/theorems/28a1b678-3c5e-437b-964f-a7c7903ab2a3
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pullback Degree Count ncard pull W eq 558ce03dd39e: P2 M Ground Theory Heights  Heights Inter Pullback Degree Count ncard pull W eq 558ce03dd39e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pullback Degree Count ncard pull W eq 558ce03dd39e construction uses the P2 M Ground Theory Heights  Heights Inter Pullback Degree Count ncard pull W eq 558ce03dd39e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NormSegreSameOrbit.lean#L59-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NormSegreSameOrbit.lean#L59-L80

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
omit [Fintype K']

theorem P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_ncard_pullW_eq_558ce03dd39e {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (w : ((k : K) → ι k) → ℂ)
    (hB : ∀ z' ∈ mcPts P', z' ∈ mcPts J' →
      (Ψ (segre fun p => z' (v p)) 0)⁻¹ • segre (fun p => z' (v p)) ≠ w) :
    {x | pullW R v Ψ x = w}.ncard = (ptsOver P' v Ψ w).ncard := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PullbackDegreeCount».«ncard_pullW_eq» := P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_ncard_pullW_eq_558ce03dd39e
