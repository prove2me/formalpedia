-- Prove2me | Theorems.Thm_P2M_PI_ZuckTensorWork_isWtOn_sigC_iff__603798d8d857
-- name    : P2M_PI_ZuckTensorWork_isWtOn_sigC_iff__603798d8d857
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:15:44.095133+00:00
-- url     : https://prove2.me/theorems/5920d25b-5765-47f7-8ce6-d55c5f0697a9
-- title:
--   P2 M PI Zuck Tensor Work is Wt On sig C iff  603798d8d857: P2 M PI Zuck Tensor Work is Wt On sig C iff  603798d8d857
-- statement:
--   The P2 M PI Zuck Tensor Work is Wt On sig C iff  603798d8d857 construction uses the P2 M PI Zuck Tensor Work is Wt On sig C iff  603798d8d857 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ConjRep.lean#L228-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ConjRep.lean#L228-L231

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

theorem P2M_PI_ZuckTensorWork_isWtOn_sigC_iff__603798d8d857 (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (μ : Fin n → ℝ) (x : Cj H) :
    IsWtOn (Kset (revE ε)) (sigC σ) μ x ↔ IsWtOn (Kset ε) σ (revP μ) (Cj.un x) := by sorry

alias «PI».«ZuckTensorWork».«isWtOn_sigC_iff'» := P2M_PI_ZuckTensorWork_isWtOn_sigC_iff__603798d8d857
