-- Prove2me | Theorems.Thm_PI_TwChrOne_Pf_isIntegralAt_superdiagonalSum
-- name    : PI.TwChrOne.Pf.isIntegralAt_superdiagonalSum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:21.530811+00:00
-- url     : https://prove2.me/theorems/5ed7a512-72f7-5bcf-a997-c116afb39809
-- title:
--   Pf: is Integral At superdiagonal Sum
-- statement:
--   The Pf construction uses the is Integral At superdiagonal Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L271-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L271-L279

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

theorem PI.TwChrOne.Pf.isIntegralAt_superdiagonalSum {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)} (hrI : ∀ (j : ℕ) i, IntAt P (r (Loc.eN E (N + c) j) i)) :
    IntAt P (Loc.n1Arg r) := by sorry
