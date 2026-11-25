-- Prove2me | Theorems.Thm_PI_HenselValuation_newton_step
-- name    : PI.HenselValuation.newton_step
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:05:56.350804+00:00
-- url     : https://prove2.me/theorems/e3861b2c-1fca-585b-abc1-482a4cc2b990
-- title:
--   Hensel Valuation: newton step
-- statement:
--   The Hensel Valuation construction uses the newton step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HenselOpenValuation/IsOpenLeVal.lean#L45-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HenselOpenValuation/IsOpenLeVal.lean#L45-L113

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

theorem PI.HenselValuation.newton_step (f : Polynomial 𝒪[F]) (a b : 𝒪[F])
    (hba : valuation F ((b - a : 𝒪[F]) : F) < valuation F ((f.derivative.eval a : 𝒪[F]) : F))
    (hfb : valuation F ((f.eval b : 𝒪[F]) : F) <
      valuation F ((f.derivative.eval a : 𝒪[F]) : F) ^ 2)
    (hne : f.eval b ≠ 0) :
    ∃ b' : 𝒪[F], valuation F ((b' - a : 𝒪[F]) : F) <
        valuation F ((f.derivative.eval a : 𝒪[F]) : F) ∧
      valuation F ((f.eval b' : 𝒪[F]) : F) < valuation F ((f.eval b : 𝒪[F]) : F) := by sorry
