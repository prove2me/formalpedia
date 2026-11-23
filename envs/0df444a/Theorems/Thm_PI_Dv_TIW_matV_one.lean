-- Prove2me | Theorems.Thm_PI_Dv_TIW_matV_one
-- name    : PI.Dv.TIW.matV_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:04.356043+00:00
-- url     : https://prove2.me/theorems/46a8808a-dfd0-4cf3-9b6b-87577fc0a1a4
-- title:
--   TIW: mat V one
-- statement:
--   The TIW construction uses the mat V one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean#L28-L31

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

theorem PI.Dv.TIW.matV_one {n : Type} [Fintype n] [DecidableEq n] :
    (matV (1 : Matrix n n K) : (n → V) →ₗ[K] (n → V)) = LinearMap.id := by sorry
