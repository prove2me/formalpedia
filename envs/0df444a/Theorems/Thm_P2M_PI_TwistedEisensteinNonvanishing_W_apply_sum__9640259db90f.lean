-- Prove2me | Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_apply_sum__9640259db90f
-- name    : P2M_PI_TwistedEisensteinNonvanishing_W_apply_sum__9640259db90f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:57:43.458663+00:00
-- url     : https://prove2.me/theorems/32d8eaeb-79dc-4331-b4f4-17a0627477f4
-- title:
--   P2 M PI Twisted Eisenstein Nonvanishing W apply sum  9640259db90f: P2 M PI Twisted Eisenstein Nonvanishing W apply sum  9640259db90f
-- statement:
--   The P2 M PI Twisted Eisenstein Nonvanishing W apply sum  9640259db90f construction uses the P2 M PI Twisted Eisenstein Nonvanishing W apply sum  9640259db90f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L77-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L77-L84

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

theorem P2M_PI_TwistedEisensteinNonvanishing_W_apply_sum__9640259db90f {N : ℕ} (f : Sp E N ≃ₗ[E] Sp E N) (v : Sp E N) (i : Fin N) :
    f v i = ∑ m : Fin N, v m * f (eN E N m.1) i := by sorry

alias «PI».«TwistedEisensteinNonvanishing».«W».«apply_sum'» := P2M_PI_TwistedEisensteinNonvanishing_W_apply_sum__9640259db90f
