-- Prove2me | Theorems.Thm_PI_Dv_TIW_matV_apply
-- name    : PI.Dv.TIW.matV_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:01.960653+00:00
-- url     : https://prove2.me/theorems/8d544cf2-8db1-4baf-b7b4-f4accb1ec22a
-- title:
--   TIW: mat V apply
-- statement:
--   The TIW construction uses the mat V apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean#L18-L20

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

theorem PI.Dv.TIW.matV_apply {n : Type} [Fintype n] (Γ : Matrix n n K) (x : n → V) (k : n) :
    matV Γ x k = ∑ l, Γ k l • x l := by sorry
