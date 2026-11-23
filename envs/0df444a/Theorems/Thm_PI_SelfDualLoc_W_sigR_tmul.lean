-- Prove2me | Theorems.Thm_PI_SelfDualLoc_W_sigR_tmul
-- name    : PI.SelfDualLoc.W.sigR_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:55.157315+00:00
-- url     : https://prove2.me/theorems/cfec6ffe-efa6-4cbd-9a6c-6bff293f0c3a
-- title:
--   W: sig R tmul
-- statement:
--   The W construction uses the sig R tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/OneTmulMemOloc.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/OneTmulMemOloc.lean#L16-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_OneTmulMemOloc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
open PI.SelfDualLoc
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem PI.SelfDualLoc.W.sigR_tmul (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (e : E) (r : R) :
    sigR σ R (e ⊗ₜ[F] r) = σ e ⊗ₜ[F] r := by sorry
