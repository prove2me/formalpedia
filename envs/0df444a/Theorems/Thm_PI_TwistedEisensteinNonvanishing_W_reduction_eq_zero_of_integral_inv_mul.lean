-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_reduction_eq_zero_of_integral_inv_mul
-- name    : PI.TwistedEisensteinNonvanishing.W.reduction_eq_zero_of_integral_inv_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:30:08.264026+00:00
-- url     : https://prove2.me/theorems/c7576f4e-fd36-4d11-abb2-d9ed1695e77c
-- title:
--   W: reduction eq zero of integral inv mul
-- statement:
--   The W construction uses the reduction eq zero of integral inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L125-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L125-L130

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
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
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem PI.TwistedEisensteinNonvanishing.W.reduction_eq_zero_of_integral_inv_mul {z : E} (hp : (Ideal.absNorm P.asIdeal).Prime) (hz : IntAt P (z / (qOf P : E))) :
    redP P z = 0 := by sorry
