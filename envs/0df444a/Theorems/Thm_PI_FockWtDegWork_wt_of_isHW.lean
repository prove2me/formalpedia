-- Prove2me | Theorems.Thm_PI_FockWtDegWork_wt_of_isHW
-- name    : PI.FockWtDegWork.wt_of_isHW
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:35.162815+00:00
-- url     : https://prove2.me/theorems/5b9801ea-5798-41a6-8737-f4fff3185c16
-- title:
--   Fock Wt Deg Work: wt of is HW
-- statement:
--   The Fock Wt Deg Work construction uses the wt of is HW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L204-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockWeightDegree/ExistsMonomialWeight.lean#L204-L210

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockWtDegWork

theorem PI.FockWtDegWork.wt_of_isHW {p q : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) (h : IsHW act μ v) :
    v ≠ 0 ∧ ∀ a, (act (Eab a a) - ((μ a : ℚ) : ℂ) • (LinearMap.id : Module.End ℂ V)) v = 0 := by sorry
