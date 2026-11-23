-- Prove2me | Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_reduction_mul__93b5aa3ac6e4
-- name    : P2M_PI_TwistedEisensteinNonvanishing_W_reduction_mul__93b5aa3ac6e4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:40.31717+00:00
-- url     : https://prove2.me/theorems/0086015c-8459-43cc-a7a2-be4d6b1b6144
-- title:
--   P2 M PI Twisted Eisenstein Nonvanishing W reduction mul  93b5aa3ac6e4: P2 M PI Twisted Eisenstein Nonvanishing W reduction mul  93b5aa3ac6e4
-- statement:
--   The P2 M PI Twisted Eisenstein Nonvanishing W reduction mul  93b5aa3ac6e4 construction uses the P2 M PI Twisted Eisenstein Nonvanishing W reduction mul  93b5aa3ac6e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IsUnitRedP.lean#L44-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IsUnitRedP.lean#L44-L60

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
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
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem P2M_PI_TwistedEisensteinNonvanishing_W_reduction_mul__93b5aa3ac6e4 {a b : E} (ha : IntAt P a) (hb : IntAt P b) : redP P (a * b) = redP P a * redP P b := by sorry

alias «PI».«TwistedEisensteinNonvanishing».«W».«reduction_mul'» := P2M_PI_TwistedEisensteinNonvanishing_W_reduction_mul__93b5aa3ac6e4
