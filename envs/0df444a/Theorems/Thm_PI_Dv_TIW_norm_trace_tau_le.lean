-- Prove2me | Theorems.Thm_PI_Dv_TIW_norm_trace_tau_le
-- name    : PI.Dv.TIW.norm_trace_tau_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:30:01.093387+00:00
-- url     : https://prove2.me/theorems/9654d675-62c2-5a1f-b809-9558ad445d07
-- title:
--   TIW: norm trace tau le
-- statement:
--   The TIW construction uses the norm trace tau le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MemOOfIsIntegral.lean#L248-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MemOOfIsIntegral.lean#L248-L252

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv NumberField
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.TIW.norm_trace_tau_le {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K G W) (g : G) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K W (τ g))‖ ≤ Module.finrank K W := by sorry
