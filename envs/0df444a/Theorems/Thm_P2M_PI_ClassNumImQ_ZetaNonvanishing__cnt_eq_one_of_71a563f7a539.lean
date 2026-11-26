-- Prove2me | Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__cnt_eq_one_of_71a563f7a539
-- name    : P2M_PI_ClassNumImQ_ZetaNonvanishing__cnt_eq_one_of_71a563f7a539
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:43:19.484079+00:00
-- url     : https://prove2.me/theorems/5b7f982b-a4ba-41d6-a81c-a6dc47bfc633
-- title:
--   P2 M PI Class Num Im Q Zeta Nonvanishing  cnt eq one of 71a563f7a539: P2 M PI Class Num Im Q Zeta Nonvanishing  cnt eq one of 71a563f7a539
-- statement:
--   The P2 M PI Class Num Im Q Zeta Nonvanishing  cnt eq one of 71a563f7a539 construction uses the P2 M PI Class Num Im Q Zeta Nonvanishing  cnt eq one of 71a563f7a539 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/GenBase.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/GenBase.lean#L42-L46

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

theorem P2M_PI_ClassNumImQ_ZetaNonvanishing__cnt_eq_one_of_71a563f7a539 {n : ℕ} (X : Ideal (𝓞 K)) (hX : Ideal.absNorm X = n)
    (h : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n → I = X) : cnt K n = 1 := by sorry

alias «PI».«ClassNumImQ».«ZetaNonvanishing₂».«cnt_eq_one_of» := P2M_PI_ClassNumImQ_ZetaNonvanishing__cnt_eq_one_of_71a563f7a539
