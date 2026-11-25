-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_DividedDifferenceVandermonde_flagIntegral_eq_mul_ddConst_53ddae8e92d5
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_DividedDifferenceVandermonde_flagIntegral_eq_mul_ddConst_53ddae8e92d5
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:19:56.294439+00:00
-- url     : https://prove2.me/theorems/1e239624-c1c6-4dd6-be8c-900ea89c19ae
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Divided Difference Vandermonde flag Integral eq mul dd Const 53ddae8e92d5: P2 M Ground Theory Heights  Heights Rest Terms Divided Difference Vandermonde
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Divided Difference Vandermonde flag Integral eq mul dd Const 53ddae8e92d5 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Divided Difference Vandermonde flag Integral eq mul dd Const 53ddae8e92d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AntisymmetrizeBlockVandermondeOf.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/AntisymmetrizeBlockVandermondeOf.lean#L21-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AntisymmetrizeBlockVandermondeOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.DividedDifferenceVandermonde

theorem P2M_GroundTheory_Heights__Heights_RestTerms_DividedDifferenceVandermonde_flagIntegral_eq_mul_ddConst_53ddae8e92d5 (f N j k : ℕ) (h : N = j + k) (Φ : RootRing f N) :
    (flagIntegral f N Φ : ℝ) =
      FlagEq.stairConst f (j + k) * IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (rootRingToReal f N j k h Φ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«DividedDifferenceVandermonde».«flagIntegral_eq_mul_ddConst» := P2M_GroundTheory_Heights__Heights_RestTerms_DividedDifferenceVandermonde_flagIntegral_eq_mul_ddConst_53ddae8e92d5
