-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_minorOn
-- name    : PositivityTheory.Rg.Sw.LVs.cdo_minorOn
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:07:13.284029+00:00
-- url     : https://prove2.me/theorems/eed3ebd9-d9f2-5674-95b9-e12237841a16
-- title:
--   LVs: cdo minor On
-- statement:
--   The LVs construction uses the cdo minor On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L97-L99

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

theorem PositivityTheory.Rg.Sw.LVs.cdo_minorOn {s : Set E} (t : Finset (Fin n)) {M : E → Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ i j, ContDiffOn ℂ ∞ (fun x => M x i j) s) : ContDiffOn ℂ ∞ (fun x => minorOn t (M x)) s := by sorry
