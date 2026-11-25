-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_dvd_of_resF_eq_zero
-- name    : PI.UnitaryGroupMassFormula.CntFormula.dvd_of_resF_eq_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:14.200984+00:00
-- url     : https://prove2.me/theorems/b9ecf4f7-c0ca-4fa4-81e3-a66ab84609e9
-- title:
--   Cnt Formula: dvd of res F eq zero
-- statement:
--   The Cnt Formula construction uses the dvd of res F eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/DensGSDvr.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/DensGSDvr.lean#L50-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_DensGSDvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula
open Classical ValuativeRel
variable (F : Type) [Field F] [ValuativeRel F]

theorem PI.UnitaryGroupMassFormula.CntFormula.dvd_of_resF_eq_zero [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {x : F}
    (hx : x ∈ 𝒪[F]) (h0 : resF F x = 0) : ∃ o : 𝒪[F], x = (ϖ : F) * o := by sorry
