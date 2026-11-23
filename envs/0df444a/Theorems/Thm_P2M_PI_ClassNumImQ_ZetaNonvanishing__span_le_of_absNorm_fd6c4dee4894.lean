-- Prove2me | Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__span_le_of_absNorm_fd6c4dee4894
-- name    : P2M_PI_ClassNumImQ_ZetaNonvanishing__span_le_of_absNorm_fd6c4dee4894
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:32.794304+00:00
-- url     : https://prove2.me/theorems/dbffce41-e0c5-4fdb-bc22-3e464f68fb22
-- title:
--   P2 M PI Class Num Im Q Zeta Nonvanishing  span le of abs Norm fd6c4dee4894: P2 M PI Class Num Im Q Zeta Nonvanishing  span le of abs Norm fd6c4dee4894
-- statement:
--   The P2 M PI Class Num Im Q Zeta Nonvanishing  span le of abs Norm fd6c4dee4894 construction uses the P2 M PI Class Num Im Q Zeta Nonvanishing  span le of abs Norm fd6c4dee4894 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/SpanNatCastSupEqTop.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/SpanNatCastSupEqTop.lean#L40-L43

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

theorem P2M_PI_ClassNumImQ_ZetaNonvanishing__span_le_of_absNorm_fd6c4dee4894 {I : Ideal (𝓞 K)} {m : ℕ} (hI : Ideal.absNorm I = m) :
    Ideal.span {(m : 𝓞 K)} ≤ I := by sorry

alias «PI».«ClassNumImQ».«ZetaNonvanishing₂».«span_le_of_absNorm» := P2M_PI_ClassNumImQ_ZetaNonvanishing__span_le_of_absNorm_fd6c4dee4894
