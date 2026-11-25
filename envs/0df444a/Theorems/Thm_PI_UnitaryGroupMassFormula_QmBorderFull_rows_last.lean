-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_rows_last
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.rows_last
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:40:36.72703+00:00
-- url     : https://prove2.me/theorems/e7cf7713-162c-5e24-88ac-8a04fc9dea5d
-- title:
--   Qm Border Full: rows last
-- statement:
--   The Qm Border Full construction uses the rows last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipOneEqSuccAbove.lean#L119-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipOneEqSuccAbove.lean#L119-L133

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

theorem PI.UnitaryGroupMassFormula.QmBorderFull.rows_last {n k : ℕ} (e es : Fin n) (v : Fin (k + 1) → Fin n) (w : Fin (k + 1)) :
    (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) ∘ (Fin.last (k + 1)).succAbove = bE e (v ∘ w.succAbove) := by sorry
