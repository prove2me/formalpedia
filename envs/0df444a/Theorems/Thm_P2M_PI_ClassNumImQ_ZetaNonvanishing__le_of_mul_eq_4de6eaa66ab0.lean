-- Prove2me | Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__le_of_mul_eq_4de6eaa66ab0
-- name    : P2M_PI_ClassNumImQ_ZetaNonvanishing__le_of_mul_eq_4de6eaa66ab0
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:55:44.176154+00:00
-- url     : https://prove2.me/theorems/84612210-20e9-484f-9bf5-7d7d097f4504
-- title:
--   P2 M PI Class Num Im Q Zeta Nonvanishing  le of mul eq 4de6eaa66ab0: P2 M PI Class Num Im Q Zeta Nonvanishing  le of mul eq 4de6eaa66ab0
-- statement:
--   The P2 M PI Class Num Im Q Zeta Nonvanishing  le of mul eq 4de6eaa66ab0 construction uses the P2 M PI Class Num Im Q Zeta Nonvanishing  le of mul eq 4de6eaa66ab0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/SpanNatCastSupEqTop.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/SpanNatCastSupEqTop.lean#L50-L56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_SpanNatCastSupEqTop
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

theorem P2M_PI_ClassNumImQ_ZetaNonvanishing__le_of_mul_eq_4de6eaa66ab0 {m n : ℕ} (hmn : m.Coprime n) {I J I' J' : Ideal (𝓞 K)}
    (hI : Ideal.absNorm I = m) (hJ' : Ideal.absNorm J' = n) (h : I * J = I' * J') : I' ≤ I := by sorry

alias «PI».«ClassNumImQ».«ZetaNonvanishing₂».«le_of_mul_eq» := P2M_PI_ClassNumImQ_ZetaNonvanishing__le_of_mul_eq_4de6eaa66ab0
