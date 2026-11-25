-- Prove2me | Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_fIdx_fPos__6ef873873a47
-- name    : P2M_PI_TwistedEisensteinNonvanishing_W_fIdx_fPos__6ef873873a47
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:57:43.995487+00:00
-- url     : https://prove2.me/theorems/d112ef97-3a87-44d0-8403-4df53f86d3b3
-- title:
--   P2 M PI Twisted Eisenstein Nonvanishing W f Idx f Pos  6ef873873a47: P2 M PI Twisted Eisenstein Nonvanishing W f Idx f Pos  6ef873873a47
-- statement:
--   The P2 M PI Twisted Eisenstein Nonvanishing W f Idx f Pos  6ef873873a47 construction uses the P2 M PI Twisted Eisenstein Nonvanishing W f Idx f Pos  6ef873873a47 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/TestFunctionPeriodicity.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/TestFunctionPeriodicity.lean#L19-L21

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

theorem P2M_PI_TwistedEisensteinNonvanishing_W_fIdx_fPos__6ef873873a47 {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) : fIdx k₀ c n (fPos k₀ c n l) = l := by sorry

alias «PI».«TwistedEisensteinNonvanishing».«W».«fIdx_fPos'» := P2M_PI_TwistedEisensteinNonvanishing_W_fIdx_fPos__6ef873873a47
