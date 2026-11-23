-- Prove2me | Theorems.Thm_PI_WHw_coeff_mem_of_eval
-- name    : PI.WHw.coeff_mem_of_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:57:47.091278+00:00
-- url     : https://prove2.me/theorems/4741c377-8218-40c5-8443-dca141a36175
-- title:
--   WHw: coeff mem of eval
-- statement:
--   The WHw construction uses the coeff mem of eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightIrreducible/ConstructionA.lean#L9-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightIrreducible/ConstructionA.lean#L9-L34

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem PI.WHw.coeff_mem_of_eval {σ : Type*} (U : Submodule ℂ (MvPolynomial σ ℂ))
    (p : Polynomial (MvPolynomial σ ℂ))
    (h : ∀ n : ℕ, p.eval (C (n : ℂ)) ∈ U) (k : ℕ) : p.coeff k ∈ U := by sorry
