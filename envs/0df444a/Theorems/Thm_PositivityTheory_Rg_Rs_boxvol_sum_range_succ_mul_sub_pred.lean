-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_boxvol_sum_range_succ_mul_sub_pred
-- name    : PositivityTheory.Rg.Rs.boxvol.sum_range_succ_mul_sub_pred
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:54:33.979751+00:00
-- url     : https://prove2.me/theorems/00d9dfab-2868-5bec-a2a3-08920ca7fcd6
-- title:
--   boxvol: sum range succ mul sub pred
-- statement:
--   The boxvol construction uses the sum range succ mul sub pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/BoxVolumes/SumRangeSuccMulSubPred.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/ExponentialNegativity/BoxVolumes/SumRangeSuccMulSubPred.lean#L7-L15

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_BoxVolumes_SumRangeSuccMulSubPred
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.boxvol

theorem PositivityTheory.Rg.Rs.boxvol.sum_range_succ_mul_sub_pred (y : ℕ → ℝ) (n : ℕ) :
    ∑ r ∈ range (n + 1), (r : ℝ) * (y (r - 1) - y r) = ∑ i ∈ range n, y i - n * y n := by sorry
