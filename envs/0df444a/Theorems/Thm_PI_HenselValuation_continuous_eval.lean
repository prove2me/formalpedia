-- Prove2me | Theorems.Thm_PI_HenselValuation_continuous_eval
-- name    : PI.HenselValuation.continuous_eval
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:14.259241+00:00
-- url     : https://prove2.me/theorems/fb2d804f-5575-4b9e-b41c-01ee09486a0d
-- title:
--   Hensel Valuation: continuous eval
-- statement:
--   The Hensel Valuation construction uses the continuous eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HenselOpenValuation/IsOpenLeVal.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HenselOpenValuation/IsOpenLeVal.lean#L41-L43

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

theorem PI.HenselValuation.continuous_eval (f : Polynomial 𝒪[F]) :
    Continuous fun y : 𝒪[F] => ((f.eval y : 𝒪[F]) : F) := by sorry
