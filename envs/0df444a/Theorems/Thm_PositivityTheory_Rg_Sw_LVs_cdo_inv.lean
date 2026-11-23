-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_inv
-- name    : PositivityTheory.Rg.Sw.LVs.cdo_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:18:12.067211+00:00
-- url     : https://prove2.me/theorems/b9b79d97-90fd-44dc-8511-30c1870f5dbd
-- title:
--   LVs: cdo inv
-- statement:
--   The LVs construction uses the cdo inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L63-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L63-L75

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

theorem PositivityTheory.Rg.Sw.LVs.cdo_inv {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set E} {M : E → Matrix ι ι ℂ}
    (hM : ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s) (h0 : ∀ x ∈ s, (M x).det ≠ 0) :
    ∀ i j, ContDiffOn ℂ ∞ (fun x => (M x)⁻¹ i j) s := by sorry
