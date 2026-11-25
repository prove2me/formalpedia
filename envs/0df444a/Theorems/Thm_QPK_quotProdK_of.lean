-- Prove2me | Theorems.Thm_QPK_quotProdK_of
-- name    : QPK.quotProdK_of
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:50:51.609873+00:00
-- url     : https://prove2.me/theorems/f7eb8611-a9a1-465b-af70-e079afa75ac8
-- title:
--   QPK: quot Prod K of
-- statement:
--   The QPK construction uses the quot Prod K of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/QuotProdKOf.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/QuotProdKOf.lean#L5-L6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_QuotProdKOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open QPK

theorem QPK.quotProdK_of (hA : GlobAsm) (hU : HaarUniq) (hL : LocPack) : PI.QuotProdK.QuotProdK := by sorry
