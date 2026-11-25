-- Prove2me | Theorems.Thm_PI_SqPairW_mem_yg
-- name    : PI.SqPairW.mem_yg
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:47:46.816417+00:00
-- url     : https://prove2.me/theorems/a7061ec5-6c84-5ded-9b06-e9c9ddcfed96
-- title:
--   Sq Pair W: mem yg
-- statement:
--   The Sq Pair W construction uses the mem yg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairGluing/ConjTransposeMemLam.lean#L97-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairGluing/ConjTransposeMemLam.lean#L97-L98

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

theorem PI.SqPairW.mem_yg {L' L'' : Submodule (𝓞 E) (Fin N → E)} {n : 𝓞 E} {x : Fin N → E} :
    x ∈ yg L' L'' n ↔ ∃ m, m ∈ L' ∧ m ∈ L'' ∧ x = (n : E) • m := by sorry
