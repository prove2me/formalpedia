-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PointsAbsIntegrable_cxHessian_tensor_73352759e667
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PointsAbsIntegrable_cxHessian_tensor_73352759e667
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:55:01.523393+00:00
-- url     : https://prove2.me/theorems/5e90e2a1-56da-5fe7-9af9-050a210ee871
-- title:
--   P2 M Ground Theory Heights  Heights Inter Points Abs Integrable cx Hessian tensor 73352759e667: P2 M Ground Theory Heights  Heights Inter Points Abs Integrable cx Hessian tensor 73352759e667
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Points Abs Integrable cx Hessian tensor 73352759e667 construction uses the P2 M Ground Theory Heights  Heights Inter Points Abs Integrable cx Hessian tensor 73352759e667 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsAbsIntegrable.lean#L26-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsAbsIntegrable.lean#L26-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAbsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAbsMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRSlotAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemiPosTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSheetHessPSD
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMixSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAbsIntegrable
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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.Inter.PointsAbsIntegrable
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_PointsAbsIntegrable_cxHessian_tensor_73352759e667 {D : ℕ} {X Y : HermLine ι} (hX : IsSmoothHerm X) (hY : IsSmoothHerm Y)
    {γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0) :
    cxHessian (fun y' => Real.log ((X.tensor Y).h (γ y'))) y =
      cxHessian (fun y' => Real.log (X.h (γ y'))) y + cxHessian (fun y' => Real.log (Y.h (γ y'))) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PointsAbsIntegrable».«cxHessian_tensor» := P2M_GroundTheory_Heights__Heights_Inter_PointsAbsIntegrable_cxHessian_tensor_73352759e667
