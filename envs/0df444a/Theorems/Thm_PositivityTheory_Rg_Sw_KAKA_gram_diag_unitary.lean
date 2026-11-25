-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_KAKA_gram_diag_unitary
-- name    : PositivityTheory.Rg.Sw.KAKA.gram_diag_unitary
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:54:52.984659+00:00
-- url     : https://prove2.me/theorems/ad387f01-df32-59ab-8722-ffc0ff15a87f
-- title:
--   KAKA: gram diag unitary
-- statement:
--   The KAKA construction uses the gram diag unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AbsoluteConvergence/GramDiagUnitary.lean#L9-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AbsoluteConvergence/GramDiagUnitary.lean#L9-L58

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

theorem PositivityTheory.Rg.Sw.KAKA.gram_diag_unitary {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (s : Fin n → ℝ)
    (hM : Mᴴ * M = diagonal (fun j => ((s j ^ 2 : ℝ) : ℂ))) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ M = U * diagonal (fun j => (s j : ℂ)) := by sorry
