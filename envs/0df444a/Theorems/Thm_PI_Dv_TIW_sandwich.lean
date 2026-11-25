-- Prove2me | Theorems.Thm_PI_Dv_TIW_sandwich
-- name    : PI.Dv.TIW.sandwich
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:23.341804+00:00
-- url     : https://prove2.me/theorems/bd25cf84-a9b0-4999-a048-ef3949dac62b
-- title:
--   TIW: sandwich
-- statement:
--   The TIW construction uses the sandwich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TraceMemOfIntR.lean#L33-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TraceMemOfIntR.lean#L33-L43

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

theorem PI.Dv.TIW.sandwich (P0 : Pair K G) (h1 : Module.finrank K (LinearMap.range (τ.asAlgebraHom (eps P0))) = 1)
    (z : MonoidAlgebra K G) :
    τ.asAlgebraHom (epsS P0 * z * eps P0) =
      LinearMap.trace K W (τ.asAlgebraHom (epsS P0 * z)) • τ.asAlgebraHom (eps P0) := by sorry
