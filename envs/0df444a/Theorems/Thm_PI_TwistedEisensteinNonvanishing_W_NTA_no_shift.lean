-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_no_shift
-- name    : PI.TwistedEisensteinNonvanishing.W.NTA.no_shift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:37:11.626686+00:00
-- url     : https://prove2.me/theorems/a9cada95-91cd-4dcf-953c-f0c5bf9a68b0
-- title:
--   NTA: no shift
-- statement:
--   The NTA construction uses the no shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IntegralApproximationByInteger.lean#L229-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IntegralApproximationByInteger.lean#L229-L243

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
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
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open PI.TwistedEisensteinNonvanishing.W.NTA
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem PI.TwistedEisensteinNonvanishing.W.NTA.no_shift (hp : (Ideal.absNorm P.asIdeal).Prime) (d : ℕ) {w w' : E} (hw : w ≠ 0) (hwi : IntAt P w⁻¹)
    (hw' : IntAt P w') (h : w = (qOf P : E) ^ (d + 1) * w') : False := by sorry
