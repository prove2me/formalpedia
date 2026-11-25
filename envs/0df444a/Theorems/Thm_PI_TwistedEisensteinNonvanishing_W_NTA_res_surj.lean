-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_res_surj
-- name    : PI.TwistedEisensteinNonvanishing.W.NTA.res_surj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:37:42.399258+00:00
-- url     : https://prove2.me/theorems/e9f9c939-33ee-4ea2-b372-70c3c77de610
-- title:
--   NTA: res surj
-- statement:
--   The NTA construction uses the res surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IntegralApproximationByInteger.lean#L85-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IntegralApproximationByInteger.lean#L85-L116

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

theorem PI.TwistedEisensteinNonvanishing.W.NTA.res_surj (hp : (Ideal.absNorm P.asIdeal).Prime) (x : 𝓞 E ⧸ P.asIdeal) :
    ∃ d : ℕ, d < qOf P ∧ Ideal.Quotient.mk P.asIdeal (d : 𝓞 E) = x := by sorry
