-- Prove2me | Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__isPrime_of_absNorm_prime_47bc113a8bf1
-- name    : P2M_PI_ClassNumImQ_ZetaNonvanishing__isPrime_of_absNorm_prime_47bc113a8bf1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:43:39.342678+00:00
-- url     : https://prove2.me/theorems/4bc9b292-f78a-4daa-8688-25f98e5fa9db
-- title:
--   P2 M PI Class Num Im Q Zeta Nonvanishing  is Prime of abs Norm prime 47bc113a8bf1: P2 M PI Class Num Im Q Zeta Nonvanishing  is Prime of abs Norm prime 47bc113a8bf1
-- statement:
--   The P2 M PI Class Num Im Q Zeta Nonvanishing  is Prime of abs Norm prime 47bc113a8bf1 construction uses the P2 M PI Class Num Im Q Zeta Nonvanishing  is Prime of abs Norm prime 47bc113a8bf1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/GenBase.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/GenBase.lean#L27-L29

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

theorem P2M_PI_ClassNumImQ_ZetaNonvanishing__isPrime_of_absNorm_prime_47bc113a8bf1 {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : Ideal.absNorm P = p) : P.IsPrime := by sorry

alias «PI».«ClassNumImQ».«ZetaNonvanishing₂».«isPrime_of_absNorm_prime» := P2M_PI_ClassNumImQ_ZetaNonvanishing__isPrime_of_absNorm_prime_47bc113a8bf1
