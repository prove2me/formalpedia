-- Prove2me | Theorems.Thm_PI_WeylForKWork_card_gt_eMi
-- name    : PI.WeylForKWork.card_gt_eMi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:49:33.115899+00:00
-- url     : https://prove2.me/theorems/4d7d99a6-6a8f-4843-80f8-0100dfa188c1
-- title:
--   Weyl For KWork: card gt e Mi
-- statement:
--   The Weyl For KWork construction uses the card gt e Mi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L98-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L98-L111

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

theorem PI.WeylForKWork.card_gt_eMi (ε : Fin N → Bool) (i : Fin (nMi ε)) :
    (univ.filter fun b => eMi ε i < b ∧ ε b = ε (eMi ε i)).card = nMi ε - 1 - (i : ℕ) := by sorry
