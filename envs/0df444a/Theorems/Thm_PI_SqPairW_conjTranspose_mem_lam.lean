-- Prove2me | Theorems.Thm_PI_SqPairW_conjTranspose_mem_lam
-- name    : PI.SqPairW.conjTranspose_mem_lam
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:25:39.644684+00:00
-- url     : https://prove2.me/theorems/83fa35a2-9b4e-4160-a48c-9755797b9c8a
-- title:
--   Sq Pair W: conj Transpose mem lam
-- statement:
--   The Sq Pair W construction uses the conj Transpose mem lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairGluing/ConjTransposeMemLam.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairGluing/ConjTransposeMemLam.lean#L38-L40

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

theorem PI.SqPairW.conjTranspose_mem_lam {L' L'' : Submodule (𝓞 E) (Fin N → E)} (hL' : IsSDG E N L')
    (hL'' : IsSDG E N L'') {e : Matrix (Fin N) (Fin N) E} (he : e ∈ lam L' L'') :
    eᴴ ∈ lam L' L'' := by sorry
