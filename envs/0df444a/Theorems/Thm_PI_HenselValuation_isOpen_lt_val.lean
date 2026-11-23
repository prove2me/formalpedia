-- Prove2me | Theorems.Thm_PI_HenselValuation_isOpen_lt_val
-- name    : PI.HenselValuation.isOpen_lt_val
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:19.585589+00:00
-- url     : https://prove2.me/theorems/6186c6ef-94c3-4889-a7fc-2560f8262c8c
-- title:
--   Hensel Valuation: is Open lt val
-- statement:
--   The Hensel Valuation construction uses the is Open lt val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HenselOpenValuation/IsOpenLeVal.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HenselOpenValuation/IsOpenLeVal.lean#L13-L23

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

theorem PI.HenselValuation.isOpen_lt_val (γ : ValueGroupWithZero F) : IsOpen {x : F | γ < valuation F x} := by sorry
