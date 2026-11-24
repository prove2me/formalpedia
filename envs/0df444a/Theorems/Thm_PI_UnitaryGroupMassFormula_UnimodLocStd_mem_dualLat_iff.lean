-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_mem_dualLat_iff
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.mem_dualLat_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:21:23.3718+00:00
-- url     : https://prove2.me/theorems/1e8c17bb-67a5-498c-9e8a-2b73eb8c8ebf
-- title:
--   Unimod Loc Std: mem dual Lat iff
-- statement:
--   The Unimod Loc Std construction uses the mem dual Lat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/ExistsGoodForm.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/ExistsGoodForm.lean#L14-L16

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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.mem_dualLat_iff (H : Sesq V) (Λ : AddSubgroup V) (x : V) :
    x ∈ dualLat H Λ ↔ ∀ y ∈ Λ, ∃ k : ℤ, altE H x y = k := by sorry
