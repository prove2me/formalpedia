-- Prove2me | Theorems.Thm_PI_FrameInd_CountsW_extZ_apply
-- name    : PI.FrameInd.CountsW.extZ_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:55:05.780443+00:00
-- url     : https://prove2.me/theorems/9964f8e5-2983-45d2-a537-8a8257a5b727
-- title:
--   Counts W: ext Z apply
-- statement:
--   The Counts W construction uses the ext Z apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/Counts.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/Counts.lean#L15-L16

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NonposCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_Counts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.FrameInd PI.FrameInd.CountsW
open PI.FrameInd

theorem PI.FrameInd.CountsW.extZ_apply {n : Type*} (p : n → Prop) [DecidablePred p] (y : {i // p i} → ℂ) (i : n) :
    extZ p y i = if h : p i then y ⟨i, h⟩ else 0 := by sorry
