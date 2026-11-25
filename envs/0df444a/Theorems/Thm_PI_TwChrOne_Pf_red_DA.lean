-- Prove2me | Theorems.Thm_PI_TwChrOne_Pf_red_DA
-- name    : PI.TwChrOne.Pf.red_DA
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:28:32.432923+00:00
-- url     : https://prove2.me/theorems/69b28e1c-a276-4d77-8726-e4d033be095e
-- title:
--   Pf: red DA
-- statement:
--   The Pf construction uses the red DA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L187-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L187-L191

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwChrOne PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
variable {n : ℕ}
variable {kj N c : ℕ}

theorem PI.TwChrOne.Pf.red_DA {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)}
    (hr : r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c)
    (i : Fin (N + c)) (hi1 : kj ≤ i.1) (hi2 : i.1 < N) (j : Fin (N + c)) (hj : ¬(kj ≤ j.1 ∧ j.1 < N)) :
    redP P (r (Loc.eN E (N + c) j.1) i) = 0 := by sorry
