-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_cont_translate__f8f9aa2815be
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_cont_translate__f8f9aa2815be
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:10:23.977747+00:00
-- url     : https://prove2.me/theorems/6faa25db-0889-5388-9644-0e2a702b6952
-- title:
--   P2 M Positivity Theory Rg Sw LVs cont translate  f8f9aa2815be: P2 M Positivity Theory Rg Sw LVs cont translate  f8f9aa2815be
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs cont translate  f8f9aa2815be construction uses the P2 M Positivity Theory Rg Sw LVs cont translate  f8f9aa2815be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L200-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L200-L226

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

theorem P2M_PositivityTheory_Rg_Sw_LVs_cont_translate__f8f9aa2815be (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (Kg : Type) [TopologicalSpace Kg] (ι : Kg → M2 n) (hι : Continuous ι) (c : Kg → ℂ) (hc : Continuous c) (N : ℕ) :
    ContinuousOn (fun y : Kg × M2 n => iteratedFDeriv ℂ N (fun x => F (ι y.1 * x) * c y.1) y.2)
      (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U}) := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«cont_translate'» := P2M_PositivityTheory_Rg_Sw_LVs_cont_translate__f8f9aa2815be
