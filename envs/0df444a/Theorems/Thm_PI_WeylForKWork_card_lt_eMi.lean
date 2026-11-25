-- Prove2me | Theorems.Thm_PI_WeylForKWork_card_lt_eMi
-- name    : PI.WeylForKWork.card_lt_eMi
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:50:08.779911+00:00
-- url     : https://prove2.me/theorems/1dc66508-66cd-5f2c-a5b1-9d7e8a02493b
-- title:
--   Weyl For KWork: card lt e Mi
-- statement:
--   The Weyl For KWork construction uses the card lt e Mi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L113-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L113-L126

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

theorem PI.WeylForKWork.card_lt_eMi (ε : Fin N → Bool) (i : Fin (nMi ε)) :
    (univ.filter fun b => b < eMi ε i ∧ ε b = ε (eMi ε i)).card = (i : ℕ) := by sorry
