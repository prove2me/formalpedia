-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_mul
-- name    : PositivityTheory.Rg.Sw.LVs.cdo_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:59:09.561666+00:00
-- url     : https://prove2.me/theorems/f1385e4d-7026-40c0-982a-a09b6a2dad52
-- title:
--   LVs: cdo mul
-- statement:
--   The LVs construction uses the cdo mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L56-L61

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem PositivityTheory.Rg.Sw.LVs.cdo_mul {ι κ μ' : Type} [Fintype ι] [Fintype κ] [Fintype μ'] {s : Set E} {M : E → Matrix ι κ ℂ}
    {N : E → Matrix κ μ' ℂ} (hM : ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s)
    (hN : ∀ i j, ContDiffOn ℂ ∞ (fun x => N x i j) s) : ∀ i j, ContDiffOn ℂ ∞ (fun x => (M x * N x) i j) s := by sorry
