-- Prove2me | Theorems.Thm_PI_ZuckTensorWork_isWtOn_sigC_iff
-- name    : PI.ZuckTensorWork.isWtOn_sigC_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:15:41.91483+00:00
-- url     : https://prove2.me/theorems/8f7de8f5-2c7d-4cce-a82d-bff951982ff4
-- title:
--   Zuck Tensor Work: is Wt On sig C iff
-- statement:
--   The Zuck Tensor Work construction uses the is Wt On sig C iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ConjRep.lean#L202-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ConjRep.lean#L202-L226

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ} {ε : Fin n → Bool}

theorem PI.ZuckTensorWork.isWtOn_sigC_iff (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (μ : Fin n → ℝ) (v : H) :
    IsWtOn (Kset ε) σ μ v ↔ IsWtOn (Kset (revE ε)) (sigC σ) (revP μ) (Cj.mk v) := by sorry
