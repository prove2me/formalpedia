-- Prove2me | Theorems.Thm_PI_WeylForKWork_false_of_neg_smul_eq_smul
-- name    : PI.WeylForKWork.false_of_neg_smul_eq_smul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:38.901924+00:00
-- url     : https://prove2.me/theorems/2e80008e-b74e-49d2-9bf0-40b64a4f4100
-- title:
--   Weyl For KWork: false of neg smul eq smul
-- statement:
--   The Weyl For KWork construction uses the false of neg smul eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Weights.lean#L83-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Weights.lean#L83-L89

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype
import Definitions.Def_Lemmata_GeneralBFactLeftVariant_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Weights
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
open PI PI.UpqRep Matrix
open scoped InnerProductSpace

theorem PI.WeylForKWork.false_of_neg_smul_eq_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (z : ℂ) (hz : z ≠ 0)
    (w : H) (hw : w ≠ 0) (h : (z * -1) • w = z • w) : False := by sorry
