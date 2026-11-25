-- Prove2me | Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__sup_parts_24c8b37f94af
-- name    : P2M_PI_ClassNumImQ_ZetaNonvanishing__sup_parts_24c8b37f94af
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:56:00.92317+00:00
-- url     : https://prove2.me/theorems/3e17a7b5-da7e-43a0-a2ba-926eb525dc35
-- title:
--   P2 M PI Class Num Im Q Zeta Nonvanishing  sup parts 24c8b37f94af: P2 M PI Class Num Im Q Zeta Nonvanishing  sup parts 24c8b37f94af
-- statement:
--   The P2 M PI Class Num Im Q Zeta Nonvanishing  sup parts 24c8b37f94af construction uses the P2 M PI Class Num Im Q Zeta Nonvanishing  sup parts 24c8b37f94af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/SpanNatCastSupEqTop.lean#L58-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/SpanNatCastSupEqTop.lean#L58-L95

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

theorem P2M_PI_ClassNumImQ_ZetaNonvanishing__sup_parts_24c8b37f94af {m n : ℕ} (hmn : m.Coprime n) (hm : 0 < m) (hn : 0 < n) {A : Ideal (𝓞 K)}
    (hA : Ideal.absNorm A = m * n) :
    (A ⊔ Ideal.span {(m : 𝓞 K)}) * (A ⊔ Ideal.span {(n : 𝓞 K)}) = A ∧
      Ideal.absNorm (A ⊔ Ideal.span {(m : 𝓞 K)}) = m ∧
      Ideal.absNorm (A ⊔ Ideal.span {(n : 𝓞 K)}) = n := by sorry

alias «PI».«ClassNumImQ».«ZetaNonvanishing₂».«sup_parts» := P2M_PI_ClassNumImQ_ZetaNonvanishing__sup_parts_24c8b37f94af
