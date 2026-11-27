-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_kunf_abs_unfold
-- name    : PositivityTheory.SiegelWeilFormula.kunf.abs_unfold
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:47.634454+00:00
-- url     : https://prove2.me/theorems/34fe3c1d-f05c-45d3-a0bc-cd540e8dc8fd
-- title:
--   kunf: abs unfold
-- statement:
--   The kunf construction uses the abs unfold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/UnfoldingCompactness/AbsUnf.lean#L10-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/UnfoldingCompactness/AbsUnf.lean#L10-L159

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_UnfoldingCompactness_AbsUnfA
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_UnfoldingCompactness_AbsUnf
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
open scoped ENNReal
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.kunf

theorem PositivityTheory.SiegelWeilFormula.kunf.abs_unfold {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] (lam : Measure V) [lam.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ]
    (𝓖 : Set V) (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam)
    {Q : Type} [Countable Q] (act : Q → Λ → Q) (hact0 : ∀ q, act q 0 = q)
    (hact : ∀ q ν ν', act (act q ν) ν' = act q (ν + ν'))
    (A : Q → V → ℂ) (hA : ∀ q, Continuous (A q)) (hAact : ∀ q ν β, A (act q ν) β = A q (β + (ν : V)))
    (χ₀ : V → ℂ) (hχc : Continuous χ₀) (hχadd : ∀ β β', χ₀ (β + β') = χ₀ β * χ₀ β') (hχΛ : ∀ ν : Λ, χ₀ (ν : V) = 1)
    (C : Set V) (hC : IsCompact C) (hcov : ∀ β, ∃ ν : Λ, β + (ν : V) ∈ C)
    (u : Q → ℝ) (hu : Summable u) (hAu : ∀ q, ∀ β ∈ C, ‖A q β‖ ≤ u q)
    (q₀ : Q) (hinj : Function.Injective (act q₀))
    (hsmall : ∀ q, (∀ ν, act q₀ ν ≠ q) → ∃ β₀, χ₀ β₀ ≠ 1 ∧ ∀ ν β, A (act q ν) (β + β₀) = A (act q ν) β) :
    Integrable (A q₀) lam ∧ Integrable (fun β => A q₀ β * χ₀ β) lam ∧
      ∫ β in 𝓖, (∑' q, A q β) * χ₀ β ∂lam = ∫ β, A q₀ β * χ₀ β ∂lam := by sorry
