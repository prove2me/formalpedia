-- Prove2me | Theorems.Thm_PI_TrDualLocW_mem_S_of_pow
-- name    : PI.TrDualLocW.mem_S_of_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:26.623015+00:00
-- url     : https://prove2.me/theorems/aa53fc7f-485c-42b7-ad7f-74129b7fbb86
-- title:
--   Tr Dual Loc W: mem S of pow
-- statement:
--   The Tr Dual Loc W construction uses the mem S of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/IsIntegralNatCast.lean#L15-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/IsIntegralNatCast.lean#L15-L87

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralOfTmulMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralNatCast
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
variable {K : Type} [Field K] [NumberField K] {ℓ : ℕ} [Fact ℓ.Prime]

theorem PI.TrDualLocW.mem_S_of_pow (y : ℚ_[ℓ] ⊗[ℚ] K) (D : ℕ) (h : ∀ n : ℕ, (ℓ : ℚ_[ℓ] ⊗[ℚ] K) ^ D * y ^ n ∈ S K ℓ) :
    y ∈ S K ℓ := by sorry
