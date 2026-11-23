-- Prove2me | Theorems.Thm_PI_Dv_TIW_rk_cut
-- name    : PI.Dv.TIW.rk_cut
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:34.303348+00:00
-- url     : https://prove2.me/theorems/6c3b20dd-bfb9-4e9b-8b05-b2346137f9b0
-- title:
--   TIW: rk cut
-- statement:
--   The TIW construction uses the rk cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/BlockHyp.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/BlockHyp.lean#L36-L38

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
  [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.TIW.rk_cut (M : Submodule (𝓞 K) V) (hM : Submodule.span K (M : Set V) = ⊤) (X : Submodule K V) :
    Formalism.HN.rkK (M ⊓ X.restrictScalars (𝓞 K)) = Module.finrank K X := by sorry
