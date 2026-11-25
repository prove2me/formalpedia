-- Prove2me | Theorems.Thm_PI_Dv_TIW_trace_mem_of_intR
-- name    : PI.Dv.TIW.trace_mem_of_intR
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:56.25273+00:00
-- url     : https://prove2.me/theorems/d5b2b9f2-f7ff-44e3-81c4-694e0d9b3a21
-- title:
--   TIW: trace mem of int R
-- statement:
--   The TIW construction uses the trace mem of int R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TraceMemOfIntR.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TraceMemOfIntR.lean#L23-L31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TraceMemOfIntR
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
  {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K G W)

theorem PI.Dv.TIW.trace_mem_of_intR (z : MonoidAlgebra K G) (hz : IntR z) :
    LinearMap.trace K W (τ.asAlgebraHom z) ∈ Set.range (algebraMap (𝓞 K) K) := by sorry
