-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_rw_last
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.rw_last
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:40:29.230839+00:00
-- url     : https://prove2.me/theorems/b3984bcf-d43f-435e-9c7a-d201bdf60da3
-- title:
--   Qm Border Full: rw last
-- statement:
--   The Qm Border Full construction uses the rw last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipOneEqSuccAbove.lean#L88-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipOneEqSuccAbove.lean#L88-L95

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipOneEqSuccAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull
open PI

theorem PI.UnitaryGroupMassFormula.QmBorderFull.rw_last {n k : ℕ} (e es : Fin n) (v : Fin (k + 1) → Fin n) (w : Fin (k + 1)) :
    (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) (Fin.last (k + 1)) = es := by sorry
