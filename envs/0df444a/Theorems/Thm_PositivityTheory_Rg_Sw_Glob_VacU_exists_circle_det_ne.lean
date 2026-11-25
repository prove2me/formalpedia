-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_Glob_VacU_exists_circle_det_ne
-- name    : PositivityTheory.Rg.Sw.Glob.VacU.exists_circle_det_ne
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:48:31.936275+00:00
-- url     : https://prove2.me/theorems/c861a6a5-4be6-4043-926f-da133f174a8e
-- title:
--   Vac U: exists circle det ne
-- statement:
--   The Vac U construction uses the exists circle det ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/ExistsCircleDetNe.lean#L11-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/ExistsCircleDetNe.lean#L11-L60

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

theorem PositivityTheory.Rg.Sw.Glob.VacU.exists_circle_det_ne (W : Matrix (Fin n) (Fin n) ℂ) : ∃ lam : ℂ, ‖lam‖ = 1 ∧ (W + lam • 1).det ≠ 0 := by sorry
