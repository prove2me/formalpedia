-- Prove2me | Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_reduction_sum__70ca31df943b
-- name    : P2M_PI_TwistedEisensteinNonvanishing_W_reduction_sum__70ca31df943b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:58:13.538359+00:00
-- url     : https://prove2.me/theorems/03d5faac-0c47-5612-8a84-85d647931978
-- title:
--   P2 M PI Twisted Eisenstein Nonvanishing W reduction sum  70ca31df943b: P2 M PI Twisted Eisenstein Nonvanishing W reduction sum  70ca31df943b
-- statement:
--   The P2 M PI Twisted Eisenstein Nonvanishing W reduction sum  70ca31df943b construction uses the P2 M PI Twisted Eisenstein Nonvanishing W reduction sum  70ca31df943b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L174-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L174-L183

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
variable (P)
variable {P}

theorem P2M_PI_TwistedEisensteinNonvanishing_W_reduction_sum__70ca31df943b {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i ∈ s, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by sorry

alias «PI».«TwistedEisensteinNonvanishing».«W».«reduction_sum'» := P2M_PI_TwistedEisensteinNonvanishing_W_reduction_sum__70ca31df943b
