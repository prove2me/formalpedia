-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_exists_not_int
-- name    : PI.TwistedEisensteinNonvanishing.W.NTA.exists_not_int
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:37:09.863936+00:00
-- url     : https://prove2.me/theorems/983e9364-6442-48a1-aa0d-d2da1523976f
-- title:
--   NTA: exists not int
-- statement:
--   The NTA construction uses the exists not int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IntegralApproximationByInteger.lean#L184-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IntegralApproximationByInteger.lean#L184-L192

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

theorem PI.TwistedEisensteinNonvanishing.W.NTA.exists_not_int (hp : (Ideal.absNorm P.asIdeal).Prime) {α : 𝓞 E} (hα : α ≠ 0) :
    ∃ K : ℕ, ¬ IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ K) := by sorry
