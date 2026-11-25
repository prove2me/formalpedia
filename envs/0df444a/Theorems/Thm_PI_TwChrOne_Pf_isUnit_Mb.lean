-- Prove2me | Theorems.Thm_PI_TwChrOne_Pf_isUnit_Mb
-- name    : PI.TwChrOne.Pf.isUnit_Mb
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:30.278225+00:00
-- url     : https://prove2.me/theorems/e40ebf6a-6d0c-46cb-895c-9af4f6c08a83
-- title:
--   Pf: is Unit Mb
-- statement:
--   The Pf construction uses the is Unit Mb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L261-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L261-L269

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

theorem PI.TwChrOne.Pf.isUnit_Mb {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)} (hr : r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) :
    IsUnit (Mb P kj N c r).det := by sorry
