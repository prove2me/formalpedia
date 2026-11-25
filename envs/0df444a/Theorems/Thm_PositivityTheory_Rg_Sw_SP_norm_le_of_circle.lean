-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_norm_le_of_circle
-- name    : PositivityTheory.Rg.Sw.SP.norm_le_of_circle
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:48.76584+00:00
-- url     : https://prove2.me/theorems/8a52ffbc-3024-473f-b5b4-5adfea419816
-- title:
--   SP: norm le of circle
-- statement:
--   The SP construction uses the norm le of circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/IteratedDerivZeroOfBound.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/IteratedDerivZeroOfBound.lean#L39-L46

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_IteratedDerivZeroOfBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP

theorem PositivityTheory.Rg.Sw.SP.norm_le_of_circle {q : ℂ → ℂ} (hq : Differentiable ℂ q) {r : ℕ} {M : ℝ}
    (hM : ∀ w : ℂ, ‖w‖ = 1 → ‖w ^ r * q w‖ ≤ M) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖q z‖ ≤ M := by sorry
