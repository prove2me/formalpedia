-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_Act_exch
-- name    : PositivityTheory.SiegelWeilFormula.Act.exch
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:27.985884+00:00
-- url     : https://prove2.me/theorems/1dd09c27-b120-5259-9fd2-4dd25432d8a8
-- title:
--   Act: exch
-- statement:
--   The Act construction uses the exch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/SiegelWeilActions/Exch.lean#L10-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/SiegelWeilActions/Exch.lean#L10-L35

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_Exch
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
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Act

theorem PositivityTheory.SiegelWeilFormula.Act.exch {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable ι] {μ : Measure α} {m : Measure β}
    [SFinite μ] [SFinite m] (g : ι → α × β → ℂ) (hi : ∀ i, Integrable (g i) (μ.prod m))
    (hs : Summable fun i => ∫ p, ‖g i p‖ ∂(μ.prod m)) :
    Summable (fun i => ∫ u, ∫ v, g i (u, v) ∂m ∂μ) ∧
      ∫ u, ∫ v, (∑' i, g i (u, v)) ∂m ∂μ = ∑' i, ∫ u, ∫ v, g i (u, v) ∂m ∂μ := by sorry
