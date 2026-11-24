-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_selfDual_img
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.selfDual_img
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:21:10.02002+00:00
-- url     : https://prove2.me/theorems/4ceb78e9-32ec-4215-a8a7-583af88511d4
-- title:
--   Unimod Loc Std: self Dual img
-- statement:
--   The Unimod Loc Std construction uses the self Dual img property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/ExistsGoodForm.lean#L22-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/ExistsGoodForm.lean#L22-L44

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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.selfDual_img (H : Sesq V) (g : V ≃ₗ[ℂ] V) (hg : IsIsom H H (g : V →ₗ[ℂ] V)) {Λ : AddSubgroup V}
    (hΛ : IsSelfDual H Λ) : IsSelfDual H (imgLat (g : V →ₗ[ℂ] V) Λ) := by sorry
