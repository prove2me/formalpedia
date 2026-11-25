-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChange_posPart_eq_ae901a283544
-- name    : P2M_GroundTheory_Heights__Heights_ChartChange_posPart_eq_ae901a283544
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:31.120843+00:00
-- url     : https://prove2.me/theorems/f4386fc3-3f19-4043-bec3-b973292c04e7
-- title:
--   P2 M Ground Theory Heights  Heights Chart Change pos Part eq ae901a283544: P2 M Ground Theory Heights  Heights Chart Change pos Part eq ae901a283544
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Change pos Part eq ae901a283544 construction uses the P2 M Ground Theory Heights  Heights Chart Change pos Part eq ae901a283544 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntChartChange.lean#L68-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntChartChange.lean#L68-L165

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntChartChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeSheetNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntChartChange
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
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.ChartChange
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartChange_posPart_eq_ae901a283544 (hNull : ChartChangeSheetNull.Statement) (hL : ChartChangeLocal.Statement)
    {J J' : Ideal (MvPolynomial (Fin n) ℂ)} {A A' : Matrix (Fin d) (Fin n) ℂ}
    {u u' : Fin n → ℂ} {U U' : Set (Fin n → ℂ)} {Φ Ψ : (Fin n → ℂ) → Fin n → ℂ}
    {f f' : (Fin n → ℂ) → ℝ} {φ φ' : Fin d → (Fin n → ℂ) → ℝ} {c : Fin d → ℝ}
    {g : Fin d → (Fin n → ℂ) → ℂ}
    (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hJ' : J'.IsPrime) (hd' : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') = d)
    (hu : linForm u ∉ J) (hu' : linForm u' ∉ J') (hA : IsFiniteProjection J A)
    (hA' : IsFiniteProjection J' A') (hU : IsOpen U) (hU' : IsOpen U')
    (hZU : zeroSet J \ {x | linEval u x = 0} ⊆ U) (hZU' : zeroSet J' \ {x | linEval u' x = 0} ⊆ U')
    (hΦ : DifferentiableOn ℂ Φ U') (hΨ : DifferentiableOn ℂ Ψ U)
    (hΦm : Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}))
    (hΨm : Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}))
    (hΨΦ : ∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x)
    (hΦΨ : ∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x)
    (hf : Measurable f) (hf' : Measurable f')
    (hff : ∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, f' x = f (Φ x))
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k)) (hφ' : ∀ k, SmoothNear (zeroSet J') (φ' k))
    (hg : ∀ k, DifferentiableOn ℂ (g k) U') (hg0 : ∀ k, ∀ x ∈ U', g k x ≠ 0)
    (hφφ : ∀ k, ∀ x ∈ U', φ' k x = φ k (Φ x) + c k * Real.log ‖g k x‖) :
    ∫⁻ y, ENNReal.ofReal (chartPosDens J' A' f' φ' y) =
      ∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartChange».«posPart_eq» := P2M_GroundTheory_Heights__Heights_ChartChange_posPart_eq_ae901a283544
