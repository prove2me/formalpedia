-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PosPartLocal_chartPosDens_eq_4dc56fd33f6f
-- name    : P2M_GroundTheory_Heights__Heights_PosPartLocal_chartPosDens_eq_4dc56fd33f6f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:01.472847+00:00
-- url     : https://prove2.me/theorems/86e47307-9c5c-43e8-a1ff-a8a6477c64d4
-- title:
--   P2 M Ground Theory Heights  Heights Pos Part Local chart Pos Dens eq 4dc56fd33f6f: P2 M Ground Theory Heights  Heights Pos Part Local chart Pos Dens eq 4dc56fd33f6f
-- statement:
--   The P2 M Ground Theory Heights  Heights Pos Part Local chart Pos Dens eq 4dc56fd33f6f construction uses the P2 M Ground Theory Heights  Heights Pos Part Local chart Pos Dens eq 4dc56fd33f6f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPosPartLocal.lean#L17-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPosPartLocal.lean#L17-L58

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.PosPartLocal
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PosPartLocal_chartPosDens_eq_4dc56fd33f6f {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {s : (Fin d → ℂ) → Fin n → ℂ} {U : Set (Fin d → ℂ)} {W E : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hsd : DifferentiableOn ℂ s U)
    (hsec : ∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : IsOpen W) (hWs : ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ s (A *ᵥ x') = x')
    (hEW : E ⊆ W) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    chartPosDens J A (E.indicator f) φ y = (U ∩ s ⁻¹' E).indicator
      (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PosPartLocal».«chartPosDens_eq» := P2M_GroundTheory_Heights__Heights_PosPartLocal_chartPosDens_eq_4dc56fd33f6f
