-- Prove2me | Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_redP_sum__a67c2a3dc9b8
-- name    : P2M_PI_TwistedEisensteinNonvanishing_W_redP_sum__a67c2a3dc9b8
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:58:53.543615+00:00
-- url     : https://prove2.me/theorems/c4b30a2a-3f24-40bb-9971-228fe8b3bf00
-- title:
--   P2 M PI Twisted Eisenstein Nonvanishing W red P sum  a67c2a3dc9b8: P2 M PI Twisted Eisenstein Nonvanishing W red P sum  a67c2a3dc9b8
-- statement:
--   The P2 M PI Twisted Eisenstein Nonvanishing W red P sum  a67c2a3dc9b8 construction uses the P2 M PI Twisted Eisenstein Nonvanishing W red P sum  a67c2a3dc9b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L136-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L136-L138

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

theorem P2M_PI_TwistedEisensteinNonvanishing_W_redP_sum__a67c2a3dc9b8 {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by sorry

alias «PI».«TwistedEisensteinNonvanishing».«W».«redP_sum'» := P2M_PI_TwistedEisensteinNonvanishing_W_redP_sum__a67c2a3dc9b8
