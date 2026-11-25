-- Prove2me | Theorems.Thm_PI_SqPairW_mem_of_local
-- name    : PI.SqPairW.mem_of_local
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:25:39.503803+00:00
-- url     : https://prove2.me/theorems/98e2d3a0-090c-4a23-a8b6-88cbbdbbf3c9
-- title:
--   Sq Pair W: mem of local
-- statement:
--   The Sq Pair W construction uses the mem of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairGluing/ConjTransposeMemLam.lean#L100-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairGluing/ConjTransposeMemLam.lean#L100-L135

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_SplitPairGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ConjTransposeMemLam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairW
open Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

theorem PI.SqPairW.mem_of_local {V : Type*} [AddCommGroup V] (Y : AddSubgroup V) (x : V)
    (h : ∀ p : ℕ, p.Prime → ∃ t : ℤ, ¬ (p : ℤ) ∣ t ∧ t • x ∈ Y) : x ∈ Y := by sorry
