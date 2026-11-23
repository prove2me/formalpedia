-- Prove2me | Theorems.Thm_PI_Dv_TIW_matV_inv_cancel
-- name    : PI.Dv.TIW.matV_inv_cancel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:57.580793+00:00
-- url     : https://prove2.me/theorems/78142e0f-cb4c-4618-b256-658ffaadbef0
-- title:
--   TIW: mat V inv cancel
-- statement:
--   The TIW construction uses the mat V inv cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean#L33-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
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
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.TIW.matV_inv_cancel {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0) (x : n → V) :
    matV A (matV A⁻¹ x) = x := by sorry
