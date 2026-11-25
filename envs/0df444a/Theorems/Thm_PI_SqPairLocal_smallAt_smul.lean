-- Prove2me | Theorems.Thm_PI_SqPairLocal_smallAt_smul
-- name    : PI.SqPairLocal.smallAt_smul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:25:04.944712+00:00
-- url     : https://prove2.me/theorems/ad07f78a-74a8-54f7-b577-fbbf62f7e377
-- title:
--   Sq Pair Local: small At smul
-- statement:
--   The Sq Pair Local construction uses the small At smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L133-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L133-L143

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
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
variable {Q : Ideal (𝓞 E)} [Q.IsPrime] {c : 𝓞 E} {L : Submodule (𝓞 E) (Fin N → E)}

theorem PI.SqPairLocal.smallAt_smul {ρ : 𝓞 E} {X : Matrix (Fin N) (Fin N) E} (hρ : Dv Q c ρ) (hX : Pres L X) :
    SmallAt Q c L ((ρ : E) • X) := by sorry
