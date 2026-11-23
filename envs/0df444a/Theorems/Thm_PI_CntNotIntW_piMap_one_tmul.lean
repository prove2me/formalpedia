-- Prove2me | Theorems.Thm_PI_CntNotIntW_piMap_one_tmul
-- name    : PI.CntNotIntW.piMap_one_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:19:11.858991+00:00
-- url     : https://prove2.me/theorems/62068c7a-b64e-46f2-bd35-2cbf44b27bf1
-- title:
--   Cnt Not Int W: pi Map one tmul
-- statement:
--   The Cnt Not Int W construction uses the pi Map one tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountNonIntegrality/DSurjDef.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountNonIntegrality/DSurjDef.lean#L19-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_DSurjDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CntNotIntW
open scoped TensorProduct

theorem PI.CntNotIntW.piMap_one_tmul (K : Type) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (Fp : Type) [Field Fp] [CharZero Fp] [Algebra ℚ_[ℓ] Fp]
    (ι : K →+* Fp) (y : K) : piMap K ℓ Fp ι (1 ⊗ₜ y) = ι y := by sorry
