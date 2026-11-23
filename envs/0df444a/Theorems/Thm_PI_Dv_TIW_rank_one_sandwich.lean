-- Prove2me | Theorems.Thm_PI_Dv_TIW_rank_one_sandwich
-- name    : PI.Dv.TIW.rank_one_sandwich
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:17.048128+00:00
-- url     : https://prove2.me/theorems/a77f845a-9c9a-4cf5-8cd9-f6cfbef93bf9
-- title:
--   TIW: rank one sandwich
-- statement:
--   The TIW construction uses the rank one sandwich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MemOOfIsIntegral.lean#L166-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MemOOfIsIntegral.lean#L166-L184

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
variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem PI.Dv.TIW.rank_one_sandwich (p : Module.End K W) (hp : p * p = p) (h1 : Module.finrank K (LinearMap.range p) = 1)
    (X : Module.End K W) : p * X * p = LinearMap.trace K W (p * X) • p := by sorry
