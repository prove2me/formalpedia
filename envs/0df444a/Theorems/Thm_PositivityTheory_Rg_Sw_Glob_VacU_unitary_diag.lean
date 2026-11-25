-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_Glob_VacU_unitary_diag
-- name    : PositivityTheory.Rg.Sw.Glob.VacU.unitary_diag
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:53:04.18738+00:00
-- url     : https://prove2.me/theorems/dd06b63a-3485-40c0-b05e-4a253ebc6536
-- title:
--   Vac U: unitary diag
-- statement:
--   The Vac U construction uses the unitary diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/ExistsCircleDetNe.lean#L62-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/ExistsCircleDetNe.lean#L62-L172

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_ExistsCircleDetNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Complex
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacU
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.Glob.VacU.unitary_diag (W : Matrix (Fin n) (Fin n) ℂ) (hW : Wᴴ * W = 1) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ), Pᴴ * P = 1 ∧ P * Pᴴ = 1 ∧ (∀ j, ‖w j‖ = 1) ∧
      W = P * diagonal w * Pᴴ := by sorry
