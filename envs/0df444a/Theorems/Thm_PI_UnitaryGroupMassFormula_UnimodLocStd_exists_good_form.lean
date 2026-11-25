-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_exists_good_form
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.exists_good_form
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:33.922456+00:00
-- url     : https://prove2.me/theorems/a0a05c93-3ad9-56ad-8968-32730843de73
-- title:
--   Unimod Loc Std: exists good form
-- statement:
--   The Unimod Loc Std construction uses the exists good form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/ExistsGoodForm.lean#L77-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/ExistsGoodForm.lean#L77-L102

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_QequivApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_ExistsGoodForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.exists_good_form {a : ℕ} {b c : ℤ} {d : ℕ} (hok : CmOK a b c d) {l : ℕ} (hl : l.Prime) :
    ∃ x y : ℤ, ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2 := by sorry
