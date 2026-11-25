-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_psi_ne
-- name    : PI.TwistedEisensteinNonvanishing.W.psi_ne
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:30:14.757619+00:00
-- url     : https://prove2.me/theorems/39f107ff-0811-4730-906f-be4d4383db09
-- title:
--   W: psi ne
-- statement:
--   The W construction uses the psi ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/TwistedEisensteinOfHypotheses.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/TwistedEisensteinOfHypotheses.lean#L11-L25

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_TwistedEisensteinOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE

theorem PI.TwistedEisensteinNonvanishing.W.psi_ne {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {D : ℕ}
    {P : HeightOneSpectrum (𝓞 E)} {psi : E → K} (hpsi : PsiOk D P psi) (z : E) : psi z ≠ 0 := by sorry
