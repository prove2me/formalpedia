-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_iSub
-- name    : PI.TwistedEisensteinNonvanishing.W.NTA.iSub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:37:19.19885+00:00
-- url     : https://prove2.me/theorems/7d5317b2-dbfe-4962-a784-cef742c4f916
-- title:
--   NTA: i Sub
-- statement:
--   The NTA construction uses the i Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IntegralApproximationByInteger.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IntegralApproximationByInteger.lean#L32-L40

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

theorem PI.TwistedEisensteinNonvanishing.W.NTA.iSub {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a - b) := by sorry
