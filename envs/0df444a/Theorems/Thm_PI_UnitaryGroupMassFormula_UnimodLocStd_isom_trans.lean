-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isom_trans
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.isom_trans
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:34:01.514816+00:00
-- url     : https://prove2.me/theorems/66847e71-5bbd-41df-b2a4-7a7a8bc6be7e
-- title:
--   Unimod Loc Std: isom trans
-- statement:
--   The Unimod Loc Std construction uses the isom trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/ExistsGoodForm.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/ExistsGoodForm.lean#L67-L73

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_QequivApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_ExistsGoodForm
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
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.isom_trans (H : Sesq V) (g σ : V ≃ₗ[ℂ] V) (hg : IsIsom H H (g : V →ₗ[ℂ] V)) (hσ : IsIsom H H (σ : V →ₗ[ℂ] V)) :
    IsIsom H H ((g.trans σ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) := by sorry
