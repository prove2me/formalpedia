-- Prove2me | Theorems.Thm_P2M_PI_ClassNumImQ_ZetaNonvanishing__span_natCast_sup_eq_top_26fc201e2cd4
-- name    : P2M_PI_ClassNumImQ_ZetaNonvanishing__span_natCast_sup_eq_top_26fc201e2cd4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:23.342401+00:00
-- url     : https://prove2.me/theorems/e8236161-db90-4def-9272-f6a0a0015919
-- title:
--   P2 M PI Class Num Im Q Zeta Nonvanishing  span nat Cast sup eq top 26fc201e2cd4: P2 M PI Class Num Im Q Zeta Nonvanishing  span nat Cast sup eq top 26fc201e2cd4
-- statement:
--   The P2 M PI Class Num Im Q Zeta Nonvanishing  span nat Cast sup eq top 26fc201e2cd4 construction uses the P2 M PI Class Num Im Q Zeta Nonvanishing  span nat Cast sup eq top 26fc201e2cd4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/SpanNatCastSupEqTop.lean#L23-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDedekindZeta/SpanNatCastSupEqTop.lean#L23-L36

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

theorem P2M_PI_ClassNumImQ_ZetaNonvanishing__span_natCast_sup_eq_top_26fc201e2cd4 {S : Type*} [CommRing S] {m n : ℕ} (h : m.Coprime n) :
    Ideal.span {(m : S)} ⊔ Ideal.span {(n : S)} = ⊤ := by sorry

alias «PI».«ClassNumImQ».«ZetaNonvanishing₂».«span_natCast_sup_eq_top» := P2M_PI_ClassNumImQ_ZetaNonvanishing__span_natCast_sup_eq_top_26fc201e2cd4
