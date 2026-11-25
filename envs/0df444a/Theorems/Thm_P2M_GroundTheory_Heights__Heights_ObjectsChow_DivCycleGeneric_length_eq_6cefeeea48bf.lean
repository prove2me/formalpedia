-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_length_eq_6cefeeea48bf
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_length_eq_6cefeeea48bf
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:12:51.992113+00:00
-- url     : https://prove2.me/theorems/a1e4fffc-f9db-4110-91ed-6245818ea206
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic length eq 6cefeeea48bf: P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic length eq 6cefeeea48bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic length eq 6cefeeea48bf construction uses the P2 M Ground Theory Heights  Heights Objects Chow Div Cycle Generic length eq 6cefeeea48bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PObjectsDivCycleGeneric.lean#L20-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PObjectsDivCycleGeneric.lean#L20-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
open MvPolynomial
variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] (S : Submonoid A)
  [IsLocalization S A']

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_length_eq_6cefeeea48bf (J W : Ideal A) [W.IsPrime] (hW : Disjoint (S : Set A) W)
    [(W.map (algebraMap A A')).IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) =
      Module.length (Localization.AtPrime (W.map (algebraMap A A')))
        (Localization.AtPrime (W.map (algebraMap A A')) ⧸
          (J.map (algebraMap A A')).map (algebraMap A' (Localization.AtPrime (W.map (algebraMap A A'))))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«DivCycleGeneric».«length_eq» := P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_length_eq_6cefeeea48bf
