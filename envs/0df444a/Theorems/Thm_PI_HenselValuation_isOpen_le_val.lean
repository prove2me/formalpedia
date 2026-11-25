-- Prove2me | Theorems.Thm_PI_HenselValuation_isOpen_le_val
-- name    : PI.HenselValuation.isOpen_le_val
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:06:01.617685+00:00
-- url     : https://prove2.me/theorems/8fc75111-a40e-4af9-bdf4-fde8db102379
-- title:
--   Hensel Valuation: is Open le val
-- statement:
--   The Hensel Valuation construction uses the is Open le val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HenselOpenValuation/IsOpenLeVal.lean#L25-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HenselOpenValuation/IsOpenLeVal.lean#L25-L39

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Hensel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HenselOpenValuation_IsOpenLeVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Polynomial Topology
open PI PI.HenselValuation
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem PI.HenselValuation.isOpen_le_val {γ : ValueGroupWithZero F} (hγ : γ ≠ 0) :
    IsOpen {x : F | γ ≤ valuation F x} := by sorry
