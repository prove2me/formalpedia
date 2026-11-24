-- Prove2me | Theorems.Thm_PI_SelfDualLoc_W_sigR_inclE
-- name    : PI.SelfDualLoc.W.sigR_inclE
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:23:30.168478+00:00
-- url     : https://prove2.me/theorems/be7ef6a4-8aaa-486a-9d07-35fb0c450e8b
-- title:
--   W: sig R incl E
-- statement:
--   The W construction uses the sig R incl E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/OneTmulMemOloc.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/OneTmulMemOloc.lean#L24-L26

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

theorem PI.SelfDualLoc.W.sigR_inclE (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (e : E) :
    sigR σ R (inclE R e) = inclE R (σ e) := by sorry
