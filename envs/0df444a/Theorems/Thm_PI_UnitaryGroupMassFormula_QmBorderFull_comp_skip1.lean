-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_comp_skip1
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.comp_skip1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:40:20.052991+00:00
-- url     : https://prove2.me/theorems/cbbe3959-de31-4f37-88e9-b1dca9803142
-- title:
--   Qm Border Full: comp skip1
-- statement:
--   The Qm Border Full construction uses the comp skip1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipOneEqSuccAbove.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipOneEqSuccAbove.lean#L29-L32

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

theorem PI.UnitaryGroupMassFormula.QmBorderFull.comp_skip1 {α : Type*} {t : ℕ} (f : Fin (t + 1) → α) (p : Fin (t + 1)) :
    f ∘ skip1 p = f ∘ p.succAbove := by sorry
