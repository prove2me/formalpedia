-- Prove2me | Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_eN_mem__2e08c6580a09
-- name    : P2M_PI_TwistedEisensteinNonvanishing_W_eN_mem__2e08c6580a09
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:58:10.604971+00:00
-- url     : https://prove2.me/theorems/6b74747d-cfc4-47f5-a385-57539d535878
-- title:
--   P2 M PI Twisted Eisenstein Nonvanishing W e N mem  2e08c6580a09: P2 M PI Twisted Eisenstein Nonvanishing W e N mem  2e08c6580a09
-- statement:
--   The P2 M PI Twisted Eisenstein Nonvanishing W e N mem  2e08c6580a09 construction uses the P2 M PI Twisted Eisenstein Nonvanishing W e N mem  2e08c6580a09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L40-L46

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

theorem P2M_PI_TwistedEisensteinNonvanishing_W_eN_mem__2e08c6580a09 (n j : ℕ) : eN E n j ∈ stdAt E n P := by sorry

alias «PI».«TwistedEisensteinNonvanishing».«W».«eN_mem'» := P2M_PI_TwistedEisensteinNonvanishing_W_eN_mem__2e08c6580a09
