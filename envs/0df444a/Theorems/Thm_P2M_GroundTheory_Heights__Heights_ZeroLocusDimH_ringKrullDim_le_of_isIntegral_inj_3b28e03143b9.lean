-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_ringKrullDim_le_of_isIntegral_inj_3b28e03143b9
-- name    : P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_ringKrullDim_le_of_isIntegral_inj_3b28e03143b9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:43:45.85054+00:00
-- url     : https://prove2.me/theorems/0b09d2b0-129a-4363-abe3-8ea998a8a755
-- title:
--   P2 M Ground Theory Heights  Heights Zero Locus Dim H ring Krull Dim le of is Integral inj 3b28e03143b9: P2 M Ground Theory Heights  Heights Zero Locus Dim H ring Krull Dim le of is Integral inj 3b28e0
-- statement:
--   The P2 M Ground Theory Heights  Heights Zero Locus Dim H ring Krull Dim le of is Integral inj 3b28e03143b9 construction uses the P2 M Ground Theory Heights  Heights Zero Locus Dim H ring Krull Dim le of is Integral inj 3b28e03143b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHAlg.lean#L12-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHAlg.lean#L12-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH

theorem P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_ringKrullDim_le_of_isIntegral_inj_3b28e03143b9 {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R] (h : Function.Injective (algebraMap A R)) :
    ringKrullDim A ≤ ringKrullDim R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ZeroLocusDimH».«ringKrullDim_le_of_isIntegral_inj» := P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_ringKrullDim_le_of_isIntegral_inj_3b28e03143b9
