-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_sum_sA_ite
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.Four.sum_sA_ite
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:40:03.815071+00:00
-- url     : https://prove2.me/theorems/dae18fee-25cf-4231-a280-295e88c9d1e5
-- title:
--   Four: sum s A ite
-- statement:
--   The Four construction uses the sum s A ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipTwoSuccAboveComp.lean#L139-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/SkipTwoSuccAboveComp.lean#L139-L142

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipTwoSuccAboveComp
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull PI.UnitaryGroupMassFormula.QmBorderFull.Four
open PI

theorem PI.UnitaryGroupMassFormula.QmBorderFull.Four.sum_sA_ite {M : Type*} [AddCommMonoid M] {k : ℕ} (w : Fin (k + 1)) (g : Fin (k + 1) → M) :
    ∑ w' : Fin (k + 1), (if w ≠ w' then g w' else 0) = ∑ j : Fin k, g (w.succAbove j) := by sorry
