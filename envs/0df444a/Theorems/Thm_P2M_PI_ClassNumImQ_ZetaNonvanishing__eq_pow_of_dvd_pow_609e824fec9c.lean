-- Prove2me | Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__eq_pow_of_dvd_pow_609e824fec9c
-- name    : P2M_PI_ClassNumImQ_ZetaNonvanishing__eq_pow_of_dvd_pow_609e824fec9c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:43:52.16504+00:00
-- url     : https://prove2.me/theorems/7adccf24-692d-42c3-bee8-becb403f991a
-- title:
--   P2 M PI Class Num Im Q Zeta Nonvanishing  eq pow of dvd pow 609e824fec9c: P2 M PI Class Num Im Q Zeta Nonvanishing  eq pow of dvd pow 609e824fec9c
-- statement:
--   The P2 M PI Class Num Im Q Zeta Nonvanishing  eq pow of dvd pow 609e824fec9c construction uses the P2 M PI Class Num Im Q Zeta Nonvanishing  eq pow of dvd pow 609e824fec9c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/GenBase.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/GenBase.lean#L37-L40

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

theorem P2M_PI_ClassNumImQ_ZetaNonvanishing__eq_pow_of_dvd_pow_609e824fec9c {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) {I : Ideal (𝓞 K)}
    {n : ℕ} (h : I ∣ P ^ n) : ∃ i ≤ n, I = P ^ i := by sorry

alias «PI».«ClassNumImQ».«ZetaNonvanishing₂».«eq_pow_of_dvd_pow» := P2M_PI_ClassNumImQ_ZetaNonvanishing__eq_pow_of_dvd_pow_609e824fec9c
