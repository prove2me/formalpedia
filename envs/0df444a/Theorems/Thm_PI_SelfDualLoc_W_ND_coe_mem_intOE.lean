-- Prove2me | Theorems.Thm_PI_SelfDualLoc_W_ND_coe_mem_intOE
-- name    : PI.SelfDualLoc.W.ND.coe_mem_intOE
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:37:01.421776+00:00
-- url     : https://prove2.me/theorems/f2c06e5d-d88d-414c-8e09-da1c1a9b7299
-- title:
--   ND: coe mem int OE
-- statement:
--   The ND construction uses the coe mem int OE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/Nondeg.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/Nondeg.lean#L20-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Nondeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W PI.SelfDualLoc.W.ND
open PI.SelfDualLoc
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem PI.SelfDualLoc.W.ND.coe_mem_intOE (a : 𝓞 E) : (a : E) ∈ intOE E := by sorry
