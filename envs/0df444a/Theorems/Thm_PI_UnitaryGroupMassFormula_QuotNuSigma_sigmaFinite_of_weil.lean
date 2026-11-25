-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QuotNuSigma_sigmaFinite_of_weil
-- name    : PI.UnitaryGroupMassFormula.QuotNuSigma.sigmaFinite_of_weil
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:32:46.97833+00:00
-- url     : https://prove2.me/theorems/0d0ad813-c829-513f-8569-d2388a00506a
-- title:
--   Quot Nu Sigma: sigma Finite of weil
-- statement:
--   The Quot Nu Sigma construction uses the sigma Finite of weil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientSigmaFiniteness/SigmaFiniteOfWeil.lean#L57-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuotientSigmaFiniteness/SigmaFiniteOfWeil.lean#L57-L117

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotNuSigma
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientSigmaFiniteness_SigmaFiniteOfWeil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QuotNuSigma
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem PI.UnitaryGroupMassFormula.QuotNuSigma.sigmaFinite_of_weil [LocallyCompactSpace G] [T2Space G]
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG] (A B : Set G) (μA μB ν : Measure G)
    (hA : SigmaFinite μA ∧ μA ≠ 0 ∧ μA Aᶜ = 0 ∧ ∀ s ∈ A, μA.map (fun x => s * x) = μA)
    (hB : SigmaFinite μB ∧ μB ≠ 0 ∧ μB Bᶜ = 0 ∧ ∀ s ∈ B, μB.map (fun x => s * x) = μB)
    (hW : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂((μA.prod μB).map (fun p => p.1 * p.2))) ∂ν) :
    SigmaFinite ν := by sorry
