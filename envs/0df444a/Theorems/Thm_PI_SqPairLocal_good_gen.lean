-- Prove2me | Theorems.Thm_PI_SqPairLocal_good_gen
-- name    : PI.SqPairLocal.good_gen
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:24:24.453145+00:00
-- url     : https://prove2.me/theorems/bf545707-cae7-52b1-a285-d791e019b51e
-- title:
--   Sq Pair Local: good gen
-- statement:
--   The Sq Pair Local construction uses the good gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/DivAtOneOfInt.lean#L190-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/DivAtOneOfInt.lean#L190-L238

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_DivAtOneOfInt
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
variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime] {N : ℕ}

theorem PI.SqPairLocal.good_gen {L : Submodule (𝓞 E) (Fin N → E)} {G : Matrix (Fin N) (Fin N) E}
    (hG1 : Gᴴ * G = 1) (hGG : G * Gᴴ = 1)
    (hD : ∀ y : Fin N → E, (∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L) ↔ ∀ i, IntAt Q ((Gᴴ *ᵥ y) i))
    {c : 𝓞 E} (hc : (c : E) ≠ 0) {f : Matrix (Fin N) (Fin N) E} (hf : ∀ i j, IntAt Q (f i j))
    (hf2 : ∀ i j, DivAt Q c ((f * f - f) i j)) (hf3 : ∀ i j, DivAt Q c ((f + fᴴ - 1) i j))
    {t : 𝓞 E} (ht : DivAt Q c ((t : E) - 1)) (ht' : DivAt Q c (star (t : E) - 1))
    (ht'' : IntAt Q (star (t : E)))
    {e : Matrix (Fin N) (Fin N) E} (he : Gᴴ * e * G = (t : E) • f) :
    SmallAt Q c L (e * e - e) ∧ SmallAt Q c L (e + eᴴ - 1) := by sorry
