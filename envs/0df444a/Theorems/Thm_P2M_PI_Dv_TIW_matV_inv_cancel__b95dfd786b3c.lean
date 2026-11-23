-- Prove2me | Theorems.Thm_P2M_PI_Dv_TIW_matV_inv_cancel__b95dfd786b3c
-- name    : P2M_PI_Dv_TIW_matV_inv_cancel__b95dfd786b3c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:08.063917+00:00
-- url     : https://prove2.me/theorems/2d83b3ef-dcb1-4589-bc07-6c89b9fd444a
-- title:
--   P2 M PI Dv TIW mat V inv cancel  b95dfd786b3c: P2 M PI Dv TIW mat V inv cancel  b95dfd786b3c
-- statement:
--   The P2 M PI Dv TIW mat V inv cancel  b95dfd786b3c construction uses the P2 M PI Dv TIW mat V inv cancel  b95dfd786b3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean#L38-L41

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

theorem P2M_PI_Dv_TIW_matV_inv_cancel__b95dfd786b3c {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A.det ≠ 0) (x : n → V) :
    matV A⁻¹ (matV A x) = x := by sorry

alias «PI».«Dv».«TIW».«matV_inv_cancel'» := P2M_PI_Dv_TIW_matV_inv_cancel__b95dfd786b3c
