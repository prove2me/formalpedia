-- Prove2me | Theorems.Thm_PI_TrDualLocW_isIntegral_of_pow_bdd
-- name    : PI.TrDualLocW.isIntegral_of_pow_bdd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:11.625741+00:00
-- url     : https://prove2.me/theorems/4c778182-5349-41e2-b6dd-9136d5bd338b
-- title:
--   Tr Dual Loc W: is Integral of pow bdd
-- statement:
--   The Tr Dual Loc W construction uses the is Integral of pow bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/IsIntegralOfTmulMem.lean#L87-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/IsIntegralOfTmulMem.lean#L87-L102

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

theorem PI.TrDualLocW.isIntegral_of_pow_bdd (s : K) (d : ℕ) (hd : d ≠ 0) (h : ∀ n : ℕ, IsIntegral ℤ ((d : K) * s ^ n)) :
    IsIntegral ℤ s := by sorry
