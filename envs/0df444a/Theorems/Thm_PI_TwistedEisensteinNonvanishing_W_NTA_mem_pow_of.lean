-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_mem_pow_of
-- name    : PI.TwistedEisensteinNonvanishing.W.NTA.mem_pow_of
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:37:12.862801+00:00
-- url     : https://prove2.me/theorems/aa944eeb-ef9a-430d-85bb-ab0c4bcd65c9
-- title:
--   NTA: mem pow of
-- statement:
--   The NTA construction uses the mem pow of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IntegralApproximationByInteger.lean#L171-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IntegralApproximationByInteger.lean#L171-L182

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

theorem PI.TwistedEisensteinNonvanishing.W.NTA.mem_pow_of (hp : (Ideal.absNorm P.asIdeal).Prime) {α : 𝓞 E} {K : ℕ}
    (h : IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ K)) : α ∈ P.asIdeal ^ K := by sorry
