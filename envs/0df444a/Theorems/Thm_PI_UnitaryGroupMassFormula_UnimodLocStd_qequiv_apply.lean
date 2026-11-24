-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_qequiv_apply
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.qequiv_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:38:31.151252+00:00
-- url     : https://prove2.me/theorems/5dd08f14-6405-4fdc-ac96-c3a730a0b5f5
-- title:
--   Unimod Loc Std: qequiv apply
-- statement:
--   The Unimod Loc Std construction uses the qequiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/QequivApply.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/QequivApply.lean#L40-L43

import Definitions.Def_Formalism_PeriodIntegrals_UnimodLocStd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_QequivApply
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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V)

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.qequiv_apply (z : V) {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) (w : V) :
    qequiv H z hc0 hc w = w - (c⁻¹ * H w z) • z := by sorry
