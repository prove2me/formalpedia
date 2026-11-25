-- Prove2me | Theorems.Thm_PI_TrDualLocW_isIntegral_of_tmul_mem
-- name    : PI.TrDualLocW.isIntegral_of_tmul_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:10.115524+00:00
-- url     : https://prove2.me/theorems/987e1e2e-c2cc-40de-beef-a30c66dd01f6
-- title:
--   Tr Dual Loc W: is Integral of tmul mem
-- statement:
--   The Tr Dual Loc W construction uses the is Integral of tmul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/IsIntegralOfTmulMem.lean#L104-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/IsIntegralOfTmulMem.lean#L104-L144

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralOfTmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.TrDualLocW
open NumberField
open scoped TensorProduct
variable (K : Type) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime]
variable {K ℓ}
variable (K ℓ)
variable {K ℓ}

theorem PI.TrDualLocW.isIntegral_of_tmul_mem (X : K) (E : ℕ) (hX : IsIntegral ℤ ((ℓ : K) ^ E * X))
    (hS : (1 ⊗ₜ X : ℚ_[ℓ] ⊗[ℚ] K) ∈ S K ℓ) : IsIntegral ℤ X := by sorry
