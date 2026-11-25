-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatPosPartLocal_ratPosDens_eq_86bec30a717e
-- name    : P2M_GroundTheory_Heights__Heights_RatPosPartLocal_ratPosDens_eq_86bec30a717e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:16:50.665927+00:00
-- url     : https://prove2.me/theorems/2feee8ab-c4ca-47b8-9fb0-590b8d927904
-- title:
--   P2 M Ground Theory Heights  Heights Rat Pos Part Local rat Pos Dens eq 86bec30a717e: P2 M Ground Theory Heights  Heights Rat Pos Part Local rat Pos Dens eq 86bec30a717e
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Pos Part Local rat Pos Dens eq 86bec30a717e construction uses the P2 M Ground Theory Heights  Heights Rat Pos Part Local rat Pos Dens eq 86bec30a717e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatPosPartLocal.lean#L25-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatPosPartLocal.lean#L25-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatPosPartLocal
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
open GroundTheory.Heights₂.Heights.RatPosPartLocal
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RatPosPartLocal_ratPosDens_eq_86bec30a717e {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} {U : Set (Fin d → ℂ)} {W E : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hsd : DifferentiableOn ℂ s U)
    (hsec : ∀ y ∈ U, s y ∈ zeroSet J ∧ eval (s y) q ≠ 0 ∧ RatChart.ratMap p q (s y) = y)
    (hW : IsOpen W)
    (hWs : ∀ x' ∈ zeroSet J ∩ W, eval x' q ≠ 0 ∧ RatChart.ratMap p q x' ∈ U ∧ s (RatChart.ratMap p q x') = x')
    (hEW : E ⊆ W) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    RatChart.ratPosDens J p q (E.indicator f) φ y = (U ∩ s ⁻¹' E).indicator
      (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatPosPartLocal».«ratPosDens_eq» := P2M_GroundTheory_Heights__Heights_RatPosPartLocal_ratPosDens_eq_86bec30a717e
