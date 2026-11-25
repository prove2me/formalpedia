-- Prove2me | Theorems.Thm_PI_SelfDualLoc_W_intOE_map
-- name    : PI.SelfDualLoc.W.intOE_map
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:23:35.8909+00:00
-- url     : https://prove2.me/theorems/69dce127-c9ef-5953-b01d-fccd5021f72c
-- title:
--   W: int OE map
-- statement:
--   The W construction uses the int OE map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/OneTmulMemOloc.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/OneTmulMemOloc.lean#L30-L34

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
variable [NumberField F] [NumberField E]

theorem PI.SelfDualLoc.W.intOE_map (σ : E →ₐ[F] E) {e : E} (he : e ∈ intOE E) : σ e ∈ intOE E := by sorry
