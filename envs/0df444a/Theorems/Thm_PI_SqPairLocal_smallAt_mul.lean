-- Prove2me | Theorems.Thm_PI_SqPairLocal_smallAt_mul
-- name    : PI.SqPairLocal.smallAt_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:31:13.34636+00:00
-- url     : https://prove2.me/theorems/f0eae365-fbac-5e59-ada5-56823ec733e9
-- title:
--   Sq Pair Local: small At mul
-- statement:
--   The Sq Pair Local construction uses the small At mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SqPairLocalOfSteps.lean#L159-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SqPairLocalOfSteps.lean#L159-L163

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
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
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {N : ℕ}
variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime] {c : 𝓞 E} {L : Submodule (𝓞 E) (Fin N → E)}

theorem PI.SqPairLocal.smallAt_mul {M B : Matrix (Fin N) (Fin N) E} (h : SmallAt Q c L M) (hB : Pres L B) :
    SmallAt Q c L (M * B) := by sorry
