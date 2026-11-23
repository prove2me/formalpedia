-- Prove2me | Theorems.Thm_PI_TrDualLocW_mem_S
-- name    : PI.TrDualLocW.mem_S
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:51.380302+00:00
-- url     : https://prove2.me/theorems/2ddf0be3-1967-49f3-ae8b-32fcbe9b55f2
-- title:
--   Tr Dual Loc W: mem S
-- statement:
--   The Tr Dual Loc W construction uses the mem S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/IsIntegralOfTmulMem.lean#L77-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/IsIntegralOfTmulMem.lean#L77-L77

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

theorem PI.TrDualLocW.mem_S {x : ℚ_[ℓ] ⊗[ℚ] K} : x ∈ S K ℓ ↔ ∀ i, (BA K ℓ).repr x i ∈ PadicInt.subring ℓ := by sorry
