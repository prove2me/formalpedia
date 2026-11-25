-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_fourier_test
-- name    : PositivityTheory.Rg.Sw.LVs.STD.fourier_test
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:22.862152+00:00
-- url     : https://prove2.me/theorems/167b3791-99e4-4180-93e4-d817be1a15c5
-- title:
--   STD: fourier test
-- statement:
--   The STD construction uses the fourier test property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiff.lean#L71-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiff.lean#L71-L108

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.STD.fourier_test (β : Matrix (Fin n) (Fin n) ℂ) (hdet : β.det = 0) {φ : Vr n → ℂ} (hφ : IsT Set.univ φ) :
    ∫ x, (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * dList (List.ofFn (ml σ)).reverse φ x) * eTr β x = 0 := by sorry
