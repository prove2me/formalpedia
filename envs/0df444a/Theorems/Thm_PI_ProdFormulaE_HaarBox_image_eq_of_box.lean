-- Prove2me | Theorems.Thm_PI_ProdFormulaE_HaarBox_image_eq_of_box
-- name    : PI.ProdFormulaE.HaarBox.image_eq_of_box
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:36:18.003873+00:00
-- url     : https://prove2.me/theorems/903df70d-e44f-471a-b5ea-bf78557a3169
-- title:
--   Haar Box: image eq of box
-- statement:
--   The Haar Box construction uses the image eq of box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarBox.lean#L140-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarBox.lean#L140-L148

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open MeasureTheory Measure ValuativeRel Topology Filter Module
open scoped NNReal ENNReal Pointwise
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable [MeasurableSpace E] [BorelSpace E]

theorem PI.ProdFormulaE.HaarBox.image_eq_of_box (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[K] E)
    (γ : ι → ValueGroupWithZero K) (hγ : ∀ i, γ i ≠ 0) (c : ℝ≥0∞)
    (hc : μ (T '' box b γ) = c * μ (box b γ)) (S : Set E) : μ (T '' S) = c * μ S := by sorry
