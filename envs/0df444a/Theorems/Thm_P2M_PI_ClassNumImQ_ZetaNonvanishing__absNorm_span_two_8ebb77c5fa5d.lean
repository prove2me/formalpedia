-- Prove2me | Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__absNorm_span_two_8ebb77c5fa5d
-- name    : P2M_PI_ClassNumImQ_ZetaNonvanishing__absNorm_span_two_8ebb77c5fa5d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:43:04.221421+00:00
-- url     : https://prove2.me/theorems/768f5aff-44e9-57cf-ace9-80b89a4cd5b2
-- title:
--   P2 M PI Class Num Im Q Zeta Nonvanishing  abs Norm span two 8ebb77c5fa5d: P2 M PI Class Num Im Q Zeta Nonvanishing  abs Norm span two 8ebb77c5fa5d
-- statement:
--   The P2 M PI Class Num Im Q Zeta Nonvanishing  abs Norm span two 8ebb77c5fa5d construction uses the P2 M PI Class Num Im Q Zeta Nonvanishing  abs Norm span two 8ebb77c5fa5d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/GenBase.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/GenBase.lean#L12-L18

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

theorem P2M_PI_ClassNumImQ_ZetaNonvanishing__absNorm_span_two_8ebb77c5fa5d (h2 : Module.finrank ℚ K = 2) (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by sorry

alias «PI».«ClassNumImQ».«ZetaNonvanishing₂».«absNorm_span_two» := P2M_PI_ClassNumImQ_ZetaNonvanishing__absNorm_span_two_8ebb77c5fa5d
