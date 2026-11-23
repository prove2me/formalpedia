-- Prove2me | Theorems.Thm_PI_Dv_TIW_tau_eps_idem
-- name    : PI.Dv.TIW.tau_eps_idem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:37.570639+00:00
-- url     : https://prove2.me/theorems/289fcb9f-9365-43be-a529-d22cb5110d9b
-- title:
--   TIW: tau eps idem
-- statement:
--   The TIW construction uses the tau eps idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TraceMemOfIntR.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TraceMemOfIntR.lean#L20-L21

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

theorem PI.Dv.TIW.tau_eps_idem (P : Pair K G) : τ.asAlgebraHom (eps P) * τ.asAlgebraHom (eps P) = τ.asAlgebraHom (eps P) := by sorry
