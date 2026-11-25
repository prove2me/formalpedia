-- Prove2me | Theorems.Thm_PI_SqPairLocal_nat_mul
-- name    : PI.SqPairLocal.nat_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:25:40.230869+00:00
-- url     : https://prove2.me/theorems/654c9bbf-464b-454e-9274-1fdc94eb49e3
-- title:
--   Sq Pair Local: nat mul
-- statement:
--   The Sq Pair Local construction uses the nat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/ExistsDenFg.lean#L121-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/ExistsDenFg.lean#L121-L127

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Lemmata_GeneralBFactLeftBis_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_ExistsDenFg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] {N : ℕ}

theorem PI.SqPairLocal.nat_mul (d : 𝓞 E) (hd : d ≠ 0) :
    ∃ d' : 𝓞 E, ((Ideal.absNorm (Ideal.span {d}) : ℕ) : 𝓞 E) = d * d' ∧
      Ideal.absNorm (Ideal.span {d}) ≠ 0 := by sorry
