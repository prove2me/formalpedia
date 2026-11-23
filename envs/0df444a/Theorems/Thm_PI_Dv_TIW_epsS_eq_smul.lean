-- Prove2me | Theorems.Thm_PI_Dv_TIW_epsS_eq_smul
-- name    : PI.Dv.TIW.epsS_eq_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:46.764089+00:00
-- url     : https://prove2.me/theorems/1677da52-038b-4cfb-b6e8-d424b92bca8a
-- title:
--   TIW: eps S eq smul
-- statement:
--   The TIW construction uses the eps S eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TraceMemOfIntR.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TraceMemOfIntR.lean#L16-L18

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

theorem PI.Dv.TIW.epsS_eq_smul (P : Pair K G) : epsS P = ((Nat.card P.H : ℕ) : K) • eps P := by sorry
