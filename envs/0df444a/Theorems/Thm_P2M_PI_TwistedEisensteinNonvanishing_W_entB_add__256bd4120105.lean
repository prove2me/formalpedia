-- Prove2me | Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_entB_add__256bd4120105
-- name    : P2M_PI_TwistedEisensteinNonvanishing_W_entB_add__256bd4120105
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:57:57.530492+00:00
-- url     : https://prove2.me/theorems/69e4a389-1cbf-55fd-ae79-e9e926f05ffe
-- title:
--   P2 M PI Twisted Eisenstein Nonvanishing W ent B add  256bd4120105: P2 M PI Twisted Eisenstein Nonvanishing W ent B add  256bd4120105
-- statement:
--   The P2 M PI Twisted Eisenstein Nonvanishing W ent B add  256bd4120105 construction uses the P2 M PI Twisted Eisenstein Nonvanishing W ent B add  256bd4120105 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/TestFunctionPeriodicity.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/TestFunctionPeriodicity.lean#L29-L32

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

theorem P2M_PI_TwistedEisensteinNonvanishing_W_entB_add__256bd4120105 {N' N : ℕ} (q k₀ c' n' c n : ℕ) (x y : HomE E N' N) (p p' : ℕ) :
    entB q k₀ c' n' c n 0 0 (x + y) p p' = entB q k₀ c' n' c n 0 0 x p p' + entB q k₀ c' n' c n 0 0 y p p' := by sorry

alias «PI».«TwistedEisensteinNonvanishing».«W».«entB_add'» := P2M_PI_TwistedEisensteinNonvanishing_W_entB_add__256bd4120105
