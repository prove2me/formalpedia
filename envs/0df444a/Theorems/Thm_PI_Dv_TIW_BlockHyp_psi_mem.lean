-- Prove2me | Theorems.Thm_PI_Dv_TIW_BlockHyp_psi_mem
-- name    : PI.Dv.TIW.BlockHyp.psi_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:45.911909+00:00
-- url     : https://prove2.me/theorems/2d019636-f2ef-455a-8b02-39b270568d15
-- title:
--   Block Hyp: psi mem
-- statement:
--   The Block Hyp construction uses the psi mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/BlockHyp.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/BlockHyp.lean#L77-L79

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
variable {X Y : Submodule K V} {Φ Ψ : Fin n → V →ₗ[K] V} {Γ : Matrix (Fin n) (Fin n) K}

theorem PI.Dv.TIW.BlockHyp.psi_mem (H : BlockHyp X Y Φ Ψ Γ) (y : V) (hy : y ∈ Y) :
    LinearMap.pi Ψ y ∈ Submodule.pi Set.univ fun _ : Fin n => X := by sorry
