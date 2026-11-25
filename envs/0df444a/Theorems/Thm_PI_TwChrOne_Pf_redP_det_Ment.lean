-- Prove2me | Theorems.Thm_PI_TwChrOne_Pf_redP_det_Ment
-- name    : PI.TwChrOne.Pf.redP_det_Ment
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:28:22.217884+00:00
-- url     : https://prove2.me/theorems/10661db7-9c1a-495f-b329-b1ab3271cee9
-- title:
--   Pf: red P det Ment
-- statement:
--   The Pf construction uses the red P det Ment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L245-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L245-L250

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

theorem PI.TwChrOne.Pf.redP_det_Ment {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)} (hrI : ∀ (j : ℕ) i, IntAt P (r (Loc.eN E (N + c) j) i)) :
    redP P (Ment kj N c r).det = (Mb P kj N c r).det := by sorry
