-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_KAKA_gram_eigen
-- name    : PositivityTheory.Rg.Sw.KAKA.gram_eigen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:06.082252+00:00
-- url     : https://prove2.me/theorems/2f106ad9-c0b5-472a-956d-6f23c7255890
-- title:
--   KAKA: gram eigen
-- statement:
--   The KAKA construction uses the gram eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AbsoluteConvergence/GramDiagUnitary.lean#L60-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AbsoluteConvergence/GramDiagUnitary.lean#L60-L73

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AbsoluteConvergence_GramDiagUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.KAKA
open Matrix

theorem PositivityTheory.Rg.Sw.KAKA.gram_eigen {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (W : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℝ), Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      (A * W)ᴴ * (A * W) = diagonal (fun j => (l j : ℂ)) := by sorry
