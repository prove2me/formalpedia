-- Prove2me | Theorems.Thm_PI_Dv_TIW_trace_tau_mem
-- name    : PI.Dv.TIW.trace_tau_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:31.110143+00:00
-- url     : https://prove2.me/theorems/238715ea-0d02-4eca-b746-3164ef898fa9
-- title:
--   TIW: trace tau mem
-- statement:
--   The TIW construction uses the trace tau mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MemOOfIsIntegral.lean#L241-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MemOOfIsIntegral.lean#L241-L246

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

theorem PI.Dv.TIW.trace_tau_mem {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K G W) (g : G) : LinearMap.trace K W (τ g) ∈ Set.range (algebraMap (𝓞 K) K) := by sorry
