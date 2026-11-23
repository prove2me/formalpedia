-- Prove2me | Theorems.Thm_PI_SelfDualLoc_W_ND_mem_intOE_iff
-- name    : PI.SelfDualLoc.W.ND.mem_intOE_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:20.835005+00:00
-- url     : https://prove2.me/theorems/e1984b4f-51d4-423e-aad2-aa1e1de0ad10
-- title:
--   ND: mem int OE iff
-- statement:
--   The ND construction uses the mem int OE iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/Nondeg.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/Nondeg.lean#L16-L18

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

theorem PI.SelfDualLoc.W.ND.mem_intOE_iff (x : E) : x ∈ intOE E ↔ ∃ a : 𝓞 E, (a : E) = x := by sorry
