-- Prove2me | Theorems.Thm_PI_GTNum_prod_pow_pow
-- name    : PI.GTNum.prod_pow_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:41.426673+00:00
-- url     : https://prove2.me/theorems/14c70998-9d90-4e94-ad71-fb37d361a415
-- title:
--   GTNum: prod pow pow
-- statement:
--   The GTNum construction uses the prod pow pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/CardEraseIccMin.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinTopCoefficient/CardEraseIccMin.lean#L35-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GTNum
open Finset

theorem PI.GTNum.prod_pow_pow {α : Type*} (s : Finset α) (B : ℤ) (m : ℕ) (e : α → ℕ) :
    ∏ x ∈ s, (B ^ m) ^ e x = B ^ (m * ∑ x ∈ s, e x) := by sorry
