-- Prove2me | Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_reduction_det__f5782d4076ff
-- name    : P2M_PI_TwistedEisensteinNonvanishing_W_reduction_det__f5782d4076ff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:00:29.812667+00:00
-- url     : https://prove2.me/theorems/c0243a63-4d62-42cd-b57b-36b183f5309b
-- title:
--   P2 M PI Twisted Eisenstein Nonvanishing W reduction det  f5782d4076ff: P2 M PI Twisted Eisenstein Nonvanishing W reduction det  f5782d4076ff
-- statement:
--   The P2 M PI Twisted Eisenstein Nonvanishing W reduction det  f5782d4076ff construction uses the P2 M PI Twisted Eisenstein Nonvanishing W reduction det  f5782d4076ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L132-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/JacobianTransformationLaw.lean#L132-L134

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

theorem P2M_PI_TwistedEisensteinNonvanishing_W_reduction_det__f5782d4076ff {m : ℕ} (M : Matrix (Fin m) (Fin m) E) (hM : ∀ s t, IntAt P (M s t)) :
    redP P M.det = (M.map (redP P)).det := by sorry

alias «PI».«TwistedEisensteinNonvanishing».«W».«reduction_det'» := P2M_PI_TwistedEisensteinNonvanishing_W_reduction_det__f5782d4076ff
