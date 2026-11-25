-- Prove2me | Theorems.Thm_PI_SqPairLocal_smallAt_add
-- name    : PI.SqPairLocal.smallAt_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:25:02.470795+00:00
-- url     : https://prove2.me/theorems/0bc8ba55-9f59-5a95-ace9-cc94dd8c3b39
-- title:
--   Sq Pair Local: small At add
-- statement:
--   The Sq Pair Local construction uses the small At add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SqPairLocalOfSteps.lean#L142-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SqPairLocalOfSteps.lean#L142-L152

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

theorem PI.SqPairLocal.smallAt_add {M M' : Matrix (Fin N) (Fin N) E} (h : SmallAt Q c L M)
    (h' : SmallAt Q c L M') : SmallAt Q c L (M + M') := by sorry
