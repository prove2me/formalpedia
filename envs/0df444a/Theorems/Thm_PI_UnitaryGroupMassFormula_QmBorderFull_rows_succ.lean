-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_rows_succ
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.rows_succ
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:39:39.156199+00:00
-- url     : https://prove2.me/theorems/2e3e833d-8079-487f-8096-a1e3ff7bb42b
-- title:
--   Qm Border Full: rows succ
-- statement:
--   The Qm Border Full construction uses the rows succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipOneEqSuccAbove.lean#L97-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipOneEqSuccAbove.lean#L97-L117

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

theorem PI.UnitaryGroupMassFormula.QmBorderFull.rows_succ {n k : ℕ} (e es : Fin n) (v : Fin (k + 1) → Fin n) (w : Fin (k + 1))
    (h : k + 1 = k + 1 - 1 + 1) :
    (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) ∘ Fin.succ =
      Fin.snoc (α := fun _ => Fin n) (v ∘ skip1 w) es ∘ Fin.cast h := by sorry
