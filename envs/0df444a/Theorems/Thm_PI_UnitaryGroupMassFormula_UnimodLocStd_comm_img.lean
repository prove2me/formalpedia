-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_comm_img
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.comm_img
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:20:57.20097+00:00
-- url     : https://prove2.me/theorems/2ea4f9be-ec8f-4734-b2c7-820a7d895b30
-- title:
--   Unimod Loc Std: comm img
-- statement:
--   The Unimod Loc Std construction uses the comm img property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/ExistsGoodForm.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/ExistsGoodForm.lean#L46-L55

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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.comm_img (g : V ≃ₗ[ℂ] V) {S Λ : AddSubgroup V}
    (hg1 : relIdx S (imgLat (g : V →ₗ[ℂ] V) S) ≠ 0) (hg2 : relIdx (imgLat (g : V →ₗ[ℂ] V) S) S ≠ 0)
    (h1 : relIdx S Λ ≠ 0) (h2 : relIdx Λ S ≠ 0) :
    relIdx S (imgLat (g : V →ₗ[ℂ] V) Λ) ≠ 0 ∧ relIdx (imgLat (g : V →ₗ[ℂ] V) Λ) S ≠ 0 := by sorry
