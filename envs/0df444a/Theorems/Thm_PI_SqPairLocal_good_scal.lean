-- Prove2me | Theorems.Thm_PI_SqPairLocal_good_scal
-- name    : PI.SqPairLocal.good_scal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:25:13.522971+00:00
-- url     : https://prove2.me/theorems/b3ab5d68-9e12-4c86-8c0d-148a60b7e4f3
-- title:
--   Sq Pair Local: good scal
-- statement:
--   The Sq Pair Local construction uses the good scal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SplitPlaceOf.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SplitPlaceOf.lean#L42-L48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SplitPlaceOf
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
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

theorem PI.SqPairLocal.good_scal {Q : Ideal (𝓞 E)} [Q.IsPrime] {c : 𝓞 E} {L' L'' : Submodule (𝓞 E) (Fin N → E)}
    {ε : 𝓞 E} (h1 : Dv Q c (ε * (ε - 1))) (h2 : Dv Q c (ε + cj E ε - 1)) :
    Good Q c L' L'' ((ε : E) • (1 : Matrix (Fin N) (Fin N) E)) := by sorry
