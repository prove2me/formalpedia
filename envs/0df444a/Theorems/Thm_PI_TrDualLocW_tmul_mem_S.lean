-- Prove2me | Theorems.Thm_PI_TrDualLocW_tmul_mem_S
-- name    : PI.TrDualLocW.tmul_mem_S
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:19.251684+00:00
-- url     : https://prove2.me/theorems/c9285ec6-d122-4e8c-bc81-1411ba0fd56d
-- title:
--   Tr Dual Loc W: tmul mem S
-- statement:
--   The Tr Dual Loc W construction uses the tmul mem S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/IsIntegralOfTmulMem.lean#L79-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/IsIntegralOfTmulMem.lean#L79-L85

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

theorem PI.TrDualLocW.tmul_mem_S (x : K) (hx : IsIntegral ℤ x) : (1 ⊗ₜ x : ℚ_[ℓ] ⊗[ℚ] K) ∈ S K ℓ := by sorry
