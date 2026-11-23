-- Prove2me | Theorems.Thm_PI_Dv_TIW_intR_sum
-- name    : PI.Dv.TIW.intR_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:14.860326+00:00
-- url     : https://prove2.me/theorems/79f2f337-6ce6-434a-ac3b-edf6ddd70e0d
-- title:
--   TIW: int R sum
-- statement:
--   The TIW construction uses the int R sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MemOOfIsIntegral.lean#L210-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MemOOfIsIntegral.lean#L210-L211

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

theorem PI.Dv.TIW.intR_sum {ι : Type} (s : Finset ι) (f : ι → MonoidAlgebra K G) (hf : ∀ i ∈ s, IntR (f i)) :
    IntR (∑ i ∈ s, f i) := by sorry
