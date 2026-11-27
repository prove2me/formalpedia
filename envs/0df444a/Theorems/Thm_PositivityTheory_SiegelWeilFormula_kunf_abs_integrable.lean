-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_kunf_abs_integrable
-- name    : PositivityTheory.SiegelWeilFormula.kunf.abs_integrable
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:25.54942+00:00
-- url     : https://prove2.me/theorems/c4731a86-d9eb-587e-ab5c-4cd03b4eabf6
-- title:
--   kunf: abs integrable
-- statement:
--   The kunf construction uses the abs integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/UnfoldingCompactness/AbsUnfB.lean#L10-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/UnfoldingCompactness/AbsUnfB.lean#L10-L58

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_UnfoldingCompactness_AbsUnfA
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_UnfoldingCompactness_AbsUnfB
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

theorem PositivityTheory.SiegelWeilFormula.kunf.abs_integrable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (lam : Measure V) [lam.IsAddHaarMeasure]
    (Λ : AddSubgroup V) [Countable Λ] (𝓖 : Set V) (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam)
    {Q : Type} [Countable Q] (act : Q → Λ → Q) (hact0 : ∀ q, act q 0 = q)
    (hact : ∀ q ν ν', act (act q ν) ν' = act q (ν + ν'))
    (A : Q → V → ℂ) (hA : ∀ q, Continuous (A q)) (hAact : ∀ q ν β, A (act q ν) β = A q (β + (ν : V)))
    (C : Set V) (hC : IsCompact C) (hcov : ∀ β, ∃ ν : Λ, β + (ν : V) ∈ C)
    (u : Q → ℝ) (hu : Summable u) (hAu : ∀ q, ∀ β ∈ C, ‖A q β‖ ≤ u q)
    (q₀ : Q) (hinj : Function.Injective (act q₀)) : Integrable (A q₀) lam := by sorry
