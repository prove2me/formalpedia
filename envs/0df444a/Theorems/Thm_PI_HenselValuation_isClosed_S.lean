-- Prove2me | Theorems.Thm_PI_HenselValuation_isClosed_S
-- name    : PI.HenselValuation.isClosed_S
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:05:42.115803+00:00
-- url     : https://prove2.me/theorems/6959700a-1aee-5e8d-b927-31746752070a
-- title:
--   Hensel Valuation: is Closed S
-- statement:
--   The Hensel Valuation construction uses the is Closed S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HenselOpenValuation/IsOpenLeVal.lean#L115-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HenselOpenValuation/IsOpenLeVal.lean#L115-L134

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

theorem PI.HenselValuation.isClosed_S (f : Polynomial 𝒪[F]) (a : 𝒪[F]) (hc0 : valuation F ((f.derivative.eval a : 𝒪[F]) : F) ≠ 0) :
    IsClosed {b : 𝒪[F] | valuation F ((b - a : 𝒪[F]) : F) <
        valuation F ((f.derivative.eval a : 𝒪[F]) : F) ∧
      valuation F ((f.eval b : 𝒪[F]) : F) ≤ valuation F ((f.eval a : 𝒪[F]) : F)} := by sorry
