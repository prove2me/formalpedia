-- Prove2me | Theorems.Thm_P2M_PI_Dv_TIW__t_apply_09160b2633db
-- name    : P2M_PI_Dv_TIW__t_apply_09160b2633db
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:05:05.233538+00:00
-- url     : https://prove2.me/theorems/8c58e505-2a1d-4a62-9e72-17aa5382b196
-- title:
--   P2 M PI Dv TIW  t apply 09160b2633db: P2 M PI Dv TIW  t apply 09160b2633db
-- statement:
--   The P2 M PI Dv TIW  t apply 09160b2633db construction uses the P2 M PI Dv TIW  t apply 09160b2633db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/BlockHyp.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/BlockHyp.lean#L52-L53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp
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
  [IsScalarTower (𝓞 K) K V] {n : ℕ}

theorem P2M_PI_Dv_TIW__t_apply_09160b2633db (Φ : Fin n → V →ₗ[K] V) (x : Fin n → V) : Φt Φ x = ∑ i, Φ i (x i) := by sorry

alias «PI».«Dv».«TIW».«Φt_apply» := P2M_PI_Dv_TIW__t_apply_09160b2633db
