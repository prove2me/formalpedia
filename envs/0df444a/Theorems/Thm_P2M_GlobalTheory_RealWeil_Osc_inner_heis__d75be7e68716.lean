-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RealWeil_Osc_inner_heis__d75be7e68716
-- name    : P2M_GlobalTheory_RealWeil_Osc_inner_heis__d75be7e68716
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:08:09.865623+00:00
-- url     : https://prove2.me/theorems/79d104b0-cd51-4601-b294-ae48cca6b64e
-- title:
--   P2 M Global Theory Real Weil Osc inner heis  d75be7e68716: P2 M Global Theory Real Weil Osc inner heis  d75be7e68716
-- statement:
--   The P2 M Global Theory Real Weil Osc inner heis  d75be7e68716 construction uses the P2 M Global Theory Real Weil Osc inner heis  d75be7e68716 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionOfGaussianPairings.lean#L204-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOscillatorActionOfGaussianPairings.lean#L204-L206

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Osc
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ ρ' : V → B →L[ℂ] B}
set_option linter.unusedSectionVars false
variable {T : B →L[ℂ] B}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Φ : B →L[ℂ] H}

theorem P2M_GlobalTheory_RealWeil_Osc_inner_heis__d75be7e68716 (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) (v : V)
    (x y : B) : inner ℂ (Φ x) (Φ (ρ v y)) = inner ℂ (Φ (ρ (-v) x)) (Φ y) := by sorry

alias «GlobalTheory».«RealWeil».«Osc».«inner_heis'» := P2M_GlobalTheory_RealWeil_Osc_inner_heis__d75be7e68716
