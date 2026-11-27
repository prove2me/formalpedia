-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KWhit_MeasG_covol_unique
-- name    : PositivityTheory.SiegelWeilFormula.KWhit.MeasG.covol_unique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:09.048143+00:00
-- url     : https://prove2.me/theorems/f544695e-9ffe-4888-84bf-16fb8cd53fbc
-- title:
--   Meas G: covol unique
-- statement:
--   The Meas G construction uses the covol unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/WhittakerCovolume/CovolUnique.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/WhittakerCovolume/CovolUnique.lean#L7-L20

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_WhittakerCovolume_CovolUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.KWhit.MeasG
open MeasureTheory

theorem PositivityTheory.SiegelWeilFormula.KWhit.MeasG.covol_unique {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ]
    {μ μ' : Measure G} [μ.IsAddHaarMeasure] [μ'.IsAddHaarMeasure] {𝓕 𝓕' : Set G}
    (h : IsAddFundamentalDomain Γ 𝓕 μ) (h' : IsAddFundamentalDomain Γ 𝓕' μ') (h1 : μ 𝓕 = 1) (h1' : μ' 𝓕' = 1) :
    μ' = μ := by sorry
