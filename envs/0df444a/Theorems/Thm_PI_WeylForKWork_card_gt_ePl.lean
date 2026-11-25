-- Prove2me | Theorems.Thm_PI_WeylForKWork_card_gt_ePl
-- name    : PI.WeylForKWork.card_gt_ePl
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:18.932883+00:00
-- url     : https://prove2.me/theorems/149b3ab4-01ba-51cf-a94a-f1adb42da545
-- title:
--   Weyl For KWork: card gt e Pl
-- statement:
--   The Weyl For KWork construction uses the card gt e Pl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L68-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L68-L81

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

theorem PI.WeylForKWork.card_gt_ePl (ε : Fin N → Bool) (i : Fin (nPl ε)) :
    (univ.filter fun b => ePl ε i < b ∧ ε b = ε (ePl ε i)).card = nPl ε - 1 - (i : ℕ) := by sorry
