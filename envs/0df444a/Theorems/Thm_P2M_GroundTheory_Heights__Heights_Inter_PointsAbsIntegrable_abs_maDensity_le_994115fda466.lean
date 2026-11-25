-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PointsAbsIntegrable_abs_maDensity_le_994115fda466
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PointsAbsIntegrable_abs_maDensity_le_994115fda466
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:23:33.11533+00:00
-- url     : https://prove2.me/theorems/626d68f3-7521-5685-b32f-05941c4c155e
-- title:
--   P2 M Ground Theory Heights  Heights Inter Points Abs Integrable abs ma Density le 994115fda466: P2 M Ground Theory Heights  Heights Inter Points Abs Integrable abs ma Density le 994115fda466
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Points Abs Integrable abs ma Density le 994115fda466 construction uses the P2 M Ground Theory Heights  Heights Inter Points Abs Integrable abs ma Density le 994115fda466 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsAbsIntegrable.lean#L46-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsAbsIntegrable.lean#L46-L90

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PointsAbsIntegrable_abs_maDensity_le_994115fda466 {P : Ideal (MRing ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {L T : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) (hT : ∀ j, IsSmoothHerm (T j))
    (hTp : ∀ j, IsSemiPosHerm (T j)) (hLTp : ∀ j, IsSemiPosHerm ((L j).tensor (T j)))
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (hS : IsSheet P Ψ y w γ) :
    |maDensity (fun j y' => pot L j (γ y')) y| ≤
      3 ^ e * maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PointsAbsIntegrable».«abs_maDensity_le» := P2M_GroundTheory_Heights__Heights_Inter_PointsAbsIntegrable_abs_maDensity_le_994115fda466
