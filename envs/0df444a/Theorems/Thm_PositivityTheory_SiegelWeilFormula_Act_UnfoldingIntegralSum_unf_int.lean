-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_UnfoldingIntegralSum_unf_int
-- name    : PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum.unf_int
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:56:49.774369+00:00
-- url     : https://prove2.me/theorems/a51101f3-bf72-4640-9bb0-579b6126e816
-- title:
--   Unfolding Integral Sum: unf int
-- statement:
--   The Unfolding Integral Sum construction uses the unf int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/SiegelWeilActions/MeasurableSh.lean#L140-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/SiegelWeilActions/MeasurableSh.lean#L140-L165

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_IsFirstChernFamily
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_MeasurableSh
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
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.deprecated false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Act PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum
variable {V A : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
  [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]

theorem PositivityTheory.SiegelWeilFormula.Act.UnfoldingIntegralSum.unf_int {Γ : AddSubgroup V} {Δ : AddSubgroup A} [Countable Γ] [Countable Δ]
    {ν : Measure V} [ν.IsAddHaarMeasure] {lam : Measure A} [lam.IsAddHaarMeasure]
    {𝓤 : Set V} (hU : IsAddFundamentalDomain Γ 𝓤 ν) (hU1 : ν 𝓤 = 1)
    (hUU : IsAddFundamentalDomain (Γ.prod Γ) (𝓤 ×ˢ 𝓤) (ν.prod ν))
    {𝓐 : Set A} (hA : IsAddFundamentalDomain Δ 𝓐 lam)
    (Λ : (V × V) ≃ₜ+ (V × V)) (hΛ : ∀ w, w ∈ Γ.prod Γ ↔ Λ w ∈ Γ.prod Γ)
    {Q : V × V → A} (hQ : Measurable Q) {Z : V → V → A} (hZ : Measurable (Function.uncurry Z))
    {g : V × A → ℂ} (hg : Measurable g) (hfin : ∫⁻ c, ‖g c‖ₑ ∂(ν.prod lam) < ⊤) :
    ∫ p, ∑' c : Γ × Δ, g (sh Λ Q Z ((c.1 : V), (c.2 : A)) p)
        ∂((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod (lam.restrict 𝓐))) =
      ∫ c, g c ∂(ν.prod lam) := by sorry
