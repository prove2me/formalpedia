-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_key_pt
-- name    : PI.TwistedEisensteinNonvanishing.W.key_pt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:54.110829+00:00
-- url     : https://prove2.me/theorems/ec0a424e-05a0-4591-84e8-280bf197da3e
-- title:
--   W: key pt
-- statement:
--   The W construction uses the key pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/TwistedEisensteinOfHypotheses.lean#L50-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/TwistedEisensteinOfHypotheses.lean#L50-L84

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

theorem PI.TwistedEisensteinNonvanishing.W.key_pt {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {D j : ℕ} (hjD : j ≤ D)
    {P : HeightOneSpectrum (𝓞 E)} {psi : E → K} (hpsi : PsiOk D P psi) {C gx gy : K} (hC : C ≠ 0)
    {cx cy c0 : E} (hg : gx = C * gy) (hc : cy = cx + c0)
    (hbx : gx ≠ 0 → IntAt P ((qOf P : E) ^ j * cx)) (hby : gy ≠ 0 → IntAt P ((qOf P : E) ^ j * cy)) :
    gx * psi (-cx) = (C * psi c0) * (gy * psi (-cy)) := by sorry
