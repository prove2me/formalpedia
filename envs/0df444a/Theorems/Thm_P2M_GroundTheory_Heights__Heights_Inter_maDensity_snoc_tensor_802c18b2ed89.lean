-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_maDensity_snoc_tensor_802c18b2ed89
-- name    : P2M_GroundTheory_Heights__Heights_Inter_maDensity_snoc_tensor_802c18b2ed89
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:35:47.813022+00:00
-- url     : https://prove2.me/theorems/32605f8d-cc55-570a-b888-ac788fe8b05f
-- title:
--   P2 M Ground Theory Heights  Heights Inter ma Density snoc tensor 802c18b2ed89: P2 M Ground Theory Heights  Heights Inter ma Density snoc tensor 802c18b2ed89
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter ma Density snoc tensor 802c18b2ed89 construction uses the P2 M Ground Theory Heights  Heights Inter ma Density snoc tensor 802c18b2ed89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRSlotAdd.lean#L48-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRSlotAdd.lean#L48-L76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMixSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRSlotAdd
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_maDensity_snoc_tensor_802c18b2ed89 {n : ℕ} (L : Fin n → HermLine ι) {A C : HermLine ι}
    (hA : IsSmoothHerm A) (hC : IsSmoothHerm C) {γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ}
    {y : Fin (n + 1) → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0) :
    maDensity (fun j y' => pot (Fin.snoc L (A.tensor C)) j (γ y')) y =
      maDensity (fun j y' => pot (Fin.snoc L A) j (γ y')) y +
        maDensity (fun j y' => pot (Fin.snoc L C) j (γ y')) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«maDensity_snoc_tensor» := P2M_GroundTheory_Heights__Heights_Inter_maDensity_snoc_tensor_802c18b2ed89
