-- Prove2me | Theorems.Thm_PI_SqPairW_mset_sub
-- name    : PI.SqPairW.mset_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:25:42.476604+00:00
-- url     : https://prove2.me/theorems/5d063b60-d12c-4573-9bf9-a1180e6b58a6
-- title:
--   Sq Pair W: mset sub
-- statement:
--   The Sq Pair W construction uses the mset sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairGluing/ConjTransposeMemLam.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairGluing/ConjTransposeMemLam.lean#L45-L51

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

theorem PI.SqPairW.mset_sub {R : Subring (Matrix (Fin N) (Fin N) E)} (hstar : ∀ x ∈ R, xᴴ ∈ R)
    {e : Matrix (Fin N) (Fin N) E} (he : e ∈ R) : ∀ M ∈ mset e, M ∈ R := by sorry
