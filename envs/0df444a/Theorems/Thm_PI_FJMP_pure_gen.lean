-- Prove2me | Theorems.Thm_PI_FJMP_pure_gen
-- name    : PI.FJMP.pure_gen
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:40.812918+00:00
-- url     : https://prove2.me/theorems/64b97a80-ad91-4657-8dad-7440a8360477
-- title:
--   FJMP: pure gen
-- statement:
--   The FJMP construction uses the pure gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L185-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L185-L234

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMP
open PI.FJM

theorem PI.FJMP.pure_gen {ι κ : Type*} [Fintype ι] [Fintype κ] (x : ι → κ → ℕ) (pos : ι → κ → Bool)
    (h : ∑ a, |∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))| = ∑ a, ∑ c, (x a c : ℤ))
    (a : ι) (c : κ) (hx : x a c ≠ 0) :
    (∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))) ≠ 0 ∧
      (pos a c = true ↔ 0 < ∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))) := by sorry
