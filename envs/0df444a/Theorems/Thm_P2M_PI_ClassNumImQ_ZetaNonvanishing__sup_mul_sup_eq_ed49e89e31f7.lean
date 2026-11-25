-- Prove2me | Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__sup_mul_sup_eq_ed49e89e31f7
-- name    : P2M_PI_ClassNumImQ_ZetaNonvanishing__sup_mul_sup_eq_ed49e89e31f7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:55:52.094401+00:00
-- url     : https://prove2.me/theorems/76b876eb-2c2b-4ae6-a59a-10ba401fa4da
-- title:
--   P2 M PI Class Num Im Q Zeta Nonvanishing  sup mul sup eq ed49e89e31f7: P2 M PI Class Num Im Q Zeta Nonvanishing  sup mul sup eq ed49e89e31f7
-- statement:
--   The P2 M PI Class Num Im Q Zeta Nonvanishing  sup mul sup eq ed49e89e31f7 construction uses the P2 M PI Class Num Im Q Zeta Nonvanishing  sup mul sup eq ed49e89e31f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/SpanNatCastSupEqTop.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/SpanNatCastSupEqTop.lean#L9-L21

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

theorem P2M_PI_ClassNumImQ_ZetaNonvanishing__sup_mul_sup_eq_ed49e89e31f7 {R : Type*} [CommRing R] (A M N : Ideal R) (hMN : M ⊔ N = ⊤)
    (h : M * N ≤ A) : (A ⊔ M) * (A ⊔ N) = A := by sorry

alias «PI».«ClassNumImQ».«ZetaNonvanishing₂».«sup_mul_sup_eq» := P2M_PI_ClassNumImQ_ZetaNonvanishing__sup_mul_sup_eq_ed49e89e31f7
