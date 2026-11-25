-- Prove2me | Theorems.Thm_PI_WeylForKWork_card_lt_ePl
-- name    : PI.WeylForKWork.card_lt_ePl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:40.845137+00:00
-- url     : https://prove2.me/theorems/6ceef148-0bf2-5cab-a03e-870de87b158c
-- title:
--   Weyl For KWork: card lt e Pl
-- statement:
--   The Weyl For KWork construction uses the card lt e Pl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L83-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L83-L96

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Formula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix Finset
variable {N : ℕ}

theorem PI.WeylForKWork.card_lt_ePl (ε : Fin N → Bool) (i : Fin (nPl ε)) :
    (univ.filter fun b => b < ePl ε i ∧ ε b = ε (ePl ε i)).card = (i : ℕ) := by sorry
