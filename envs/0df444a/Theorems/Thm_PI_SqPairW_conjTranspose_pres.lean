-- Prove2me | Theorems.Thm_PI_SqPairW_conjTranspose_pres
-- name    : PI.SqPairW.conjTranspose_pres
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:25:15.469612+00:00
-- url     : https://prove2.me/theorems/313b81b0-163b-4917-9723-ef694072c11b
-- title:
--   Sq Pair W: conj Transpose pres
-- statement:
--   The Sq Pair W construction uses the conj Transpose pres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairGluing/ConjTransposeMemLam.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairGluing/ConjTransposeMemLam.lean#L29-L36

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

theorem PI.SqPairW.conjTranspose_pres {L : Submodule (𝓞 E) (Fin N → E)} (hL : IsSDG E N L)
    {e : Matrix (Fin N) (Fin N) E} (he : ∀ y ∈ L, e *ᵥ y ∈ L) : ∀ y ∈ L, eᴴ *ᵥ y ∈ L := by sorry
