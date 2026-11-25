-- Prove2me | Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_fPos_lt__b0c789d9c295
-- name    : P2M_PI_TwistedEisensteinNonvanishing_W_fPos_lt__b0c789d9c295
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:58:38.100053+00:00
-- url     : https://prove2.me/theorems/d4448d56-27a7-4f17-9cc5-5e9b01738c28
-- title:
--   P2 M PI Twisted Eisenstein Nonvanishing W f Pos lt  b0c789d9c295: P2 M PI Twisted Eisenstein Nonvanishing W f Pos lt  b0c789d9c295
-- statement:
--   The P2 M PI Twisted Eisenstein Nonvanishing W f Pos lt  b0c789d9c295 construction uses the P2 M PI Twisted Eisenstein Nonvanishing W f Pos lt  b0c789d9c295 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/TestFunctionPeriodicity.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/TestFunctionPeriodicity.lean#L15-L17

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_TestFunctionPeriodicity
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

theorem P2M_PI_TwistedEisensteinNonvanishing_W_fPos_lt__b0c789d9c295 {k₀ c n l : ℕ} (_hk : k₀ ≤ n) (hl : l < n + c) : fPos k₀ c n l < n + c := by sorry

alias «PI».«TwistedEisensteinNonvanishing».«W».«fPos_lt'» := P2M_PI_TwistedEisensteinNonvanishing_W_fPos_lt__b0c789d9c295
