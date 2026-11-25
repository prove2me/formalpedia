-- Prove2me | Theorems.Thm_P2M_PI_Dv_TIW__t_apply_0ce0de5f4d20
-- name    : P2M_PI_Dv_TIW__t_apply_0ce0de5f4d20
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:57:10.474625+00:00
-- url     : https://prove2.me/theorems/3eeb83ea-9870-4a64-a6c5-34e694821b20
-- title:
--   P2 M PI Dv TIW  t apply 0ce0de5f4d20: P2 M PI Dv TIW  t apply 0ce0de5f4d20
-- statement:
--   The P2 M PI Dv TIW  t apply 0ce0de5f4d20 construction uses the P2 M PI Dv TIW  t apply 0ce0de5f4d20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/BlockHyp.lean#L55-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/BlockHyp.lean#L55-L55

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

theorem P2M_PI_Dv_TIW__t_apply_0ce0de5f4d20 (Ψ : Fin n → V →ₗ[K] V) (y : V) (j : Fin n) : (LinearMap.pi Ψ) y j = Ψ j y := by sorry

alias «PI».«Dv».«TIW».«Ψt_apply» := P2M_PI_Dv_TIW__t_apply_0ce0de5f4d20
