-- Prove2me | Theorems.Thm_PI_TwChrOne_Pf_inX_eN
-- name    : PI.TwChrOne.Pf.inX_eN
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:14.963069+00:00
-- url     : https://prove2.me/theorems/7605507e-449a-587d-a881-033dc3b99e02
-- title:
--   Pf: in X e N
-- statement:
--   The Pf construction uses the in X e N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L281-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L281-L289

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

theorem PI.TwChrOne.Pf.inX_eN {j : ℕ} (hj : j < N) : Loc.inX E N c (Loc.eN E N j) = Loc.eN E (N + c) j := by sorry
