-- Prove2me | Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__ne_bot_of_absNorm_8507f2b055c6
-- name    : P2M_PI_ClassNumImQ_ZetaNonvanishing__ne_bot_of_absNorm_8507f2b055c6
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:43:46.485622+00:00
-- url     : https://prove2.me/theorems/221c51ab-b47b-41c0-b3f9-62003ebc5e73
-- title:
--   P2 M PI Class Num Im Q Zeta Nonvanishing  ne bot of abs Norm 8507f2b055c6: P2 M PI Class Num Im Q Zeta Nonvanishing  ne bot of abs Norm 8507f2b055c6
-- statement:
--   The P2 M PI Class Num Im Q Zeta Nonvanishing  ne bot of abs Norm 8507f2b055c6 construction uses the P2 M PI Class Num Im Q Zeta Nonvanishing  ne bot of abs Norm 8507f2b055c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/GenBase.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/GenBase.lean#L31-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_SpanNatCastSupEqTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_GenBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.ClassNumImQ PI.ClassNumImQ.ZetaNonvanishing₂
variable {K : Type} [Field K] [NumberField K]

theorem P2M_PI_ClassNumImQ_ZetaNonvanishing__ne_bot_of_absNorm_8507f2b055c6 {P : Ideal (𝓞 K)} {n : ℕ} (hP : Ideal.absNorm P = n) (hn : n ≠ 0) :
    P ≠ ⊥ := by sorry

alias «PI».«ClassNumImQ».«ZetaNonvanishing₂».«ne_bot_of_absNorm» := P2M_PI_ClassNumImQ_ZetaNonvanishing__ne_bot_of_absNorm_8507f2b055c6
