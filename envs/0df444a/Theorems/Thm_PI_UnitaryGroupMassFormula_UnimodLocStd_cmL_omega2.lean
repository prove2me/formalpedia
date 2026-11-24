-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_cmL_omega2
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.cmL_omega2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:12:29.623479+00:00
-- url     : https://prove2.me/theorems/1e829c10-8182-472c-8b0c-d1ce610c54ce
-- title:
--   Unimod Loc Std: cm L omega2
-- statement:
--   The Unimod Loc Std construction uses the cm L omega2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/CommOfBounded.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/CommOfBounded.lean#L15-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.cmL_omega2 : (cmL a b d ha hd lam hlam).ω₂ = lam * cmTheta b d := by sorry
