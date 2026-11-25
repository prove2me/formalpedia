-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_qequiv_isom
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.qequiv_isom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:40:57.382104+00:00
-- url     : https://prove2.me/theorems/8d070753-819e-4760-93f9-88517c8066a8
-- title:
--   Unimod Loc Std: qequiv isom
-- statement:
--   The Unimod Loc Std construction uses the qequiv isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/QequivApply.lean#L45-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/QequivApply.lean#L45-L54

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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.qequiv_isom (hsym : ∀ x y, H y x = conj (H x y)) (z : V) {c : ℂ} (hc0 : c ≠ 0)
    (hc : c + conj c = H z z) : IsIsom H H (qequiv H z hc0 hc : V →ₗ[ℂ] V) := by sorry
