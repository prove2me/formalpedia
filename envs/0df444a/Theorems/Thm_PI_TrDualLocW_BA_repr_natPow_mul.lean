-- Prove2me | Theorems.Thm_PI_TrDualLocW_BA_repr_natPow_mul
-- name    : PI.TrDualLocW.BA_repr_natPow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:08.386401+00:00
-- url     : https://prove2.me/theorems/52574c12-c47d-4b2b-b1d4-1d4477dffedd
-- title:
--   Tr Dual Loc W: BA repr nat Pow mul
-- statement:
--   The Tr Dual Loc W construction uses the BA repr nat Pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/IsIntegralOfTmulMem.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/IsIntegralOfTmulMem.lean#L30-L34

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

theorem PI.TrDualLocW.BA_repr_natPow_mul (D : ℕ) (x : ℚ_[ℓ] ⊗[ℚ] K) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    (BA K ℓ).repr ((ℓ : ℚ_[ℓ] ⊗[ℚ] K) ^ D * x) i = (ℓ : ℚ_[ℓ]) ^ D * (BA K ℓ).repr x i := by sorry
