-- Prove2me | Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__cnt_eq_zero_of_8b919f503d1d
-- name    : P2M_PI_ClassNumImQ_ZetaNonvanishing__cnt_eq_zero_of_8b919f503d1d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:53.249282+00:00
-- url     : https://prove2.me/theorems/5a582f45-6398-5a27-b063-665b826554bd
-- title:
--   P2 M PI Class Num Im Q Zeta Nonvanishing  cnt eq zero of 8b919f503d1d: P2 M PI Class Num Im Q Zeta Nonvanishing  cnt eq zero of 8b919f503d1d
-- statement:
--   The P2 M PI Class Num Im Q Zeta Nonvanishing  cnt eq zero of 8b919f503d1d construction uses the P2 M PI Class Num Im Q Zeta Nonvanishing  cnt eq zero of 8b919f503d1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/GenBase.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/GenBase.lean#L48-L51

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

theorem P2M_PI_ClassNumImQ_ZetaNonvanishing__cnt_eq_zero_of_8b919f503d1d {n : ℕ} (h : ∀ I : Ideal (𝓞 K), Ideal.absNorm I ≠ n) : cnt K n = 0 := by sorry

alias «PI».«ClassNumImQ».«ZetaNonvanishing₂».«cnt_eq_zero_of» := P2M_PI_ClassNumImQ_ZetaNonvanishing__cnt_eq_zero_of_8b919f503d1d
