-- Prove2me | Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__dvd_span_pow_of_absNorm_4b014b49b33f
-- name    : P2M_PI_ClassNumImQ_ZetaNonvanishing__dvd_span_pow_of_absNorm_4b014b49b33f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:43:35.258515+00:00
-- url     : https://prove2.me/theorems/9c0515ac-20e5-47e5-82cc-5f6508fff06c
-- title:
--   P2 M PI Class Num Im Q Zeta Nonvanishing  dvd span pow of abs Norm 4b014b49b33f: P2 M PI Class Num Im Q Zeta Nonvanishing  dvd span pow of abs Norm 4b014b49b33f
-- statement:
--   The P2 M PI Class Num Im Q Zeta Nonvanishing  dvd span pow of abs Norm 4b014b49b33f construction uses the P2 M PI Class Num Im Q Zeta Nonvanishing  dvd span pow of abs Norm 4b014b49b33f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/GenBase.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/GenBase.lean#L20-L25

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

theorem P2M_PI_ClassNumImQ_ZetaNonvanishing__dvd_span_pow_of_absNorm_4b014b49b33f {p k : ℕ} {I : Ideal (𝓞 K)} (hI : Ideal.absNorm I = p ^ k) :
    I ∣ Ideal.span {(p : 𝓞 K)} ^ k := by sorry

alias «PI».«ClassNumImQ».«ZetaNonvanishing₂».«dvd_span_pow_of_absNorm» := P2M_PI_ClassNumImQ_ZetaNonvanishing__dvd_span_pow_of_absNorm_4b014b49b33f
