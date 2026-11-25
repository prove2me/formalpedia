-- Prove2me | Theorems.Thm_PI_Dv_TIW_cut_span
-- name    : PI.Dv.TIW.cut_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:45.489676+00:00
-- url     : https://prove2.me/theorems/06dac66e-f37a-4fff-8799-9ef429a16aea
-- title:
--   TIW: cut span
-- statement:
--   The TIW construction uses the cut span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/BlockHyp.lean#L20-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/BlockHyp.lean#L20-L34

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

theorem PI.Dv.TIW.cut_span (M : Submodule (𝓞 K) V) (hM : Submodule.span K (M : Set V) = ⊤) (X : Submodule K V) :
    Submodule.span K ((M ⊓ X.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = X := by sorry
