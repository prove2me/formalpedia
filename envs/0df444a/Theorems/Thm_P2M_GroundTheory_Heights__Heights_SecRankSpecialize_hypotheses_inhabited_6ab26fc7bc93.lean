-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SecRankSpecialize_hypotheses_inhabited_6ab26fc7bc93
-- name    : P2M_GroundTheory_Heights__Heights_SecRankSpecialize_hypotheses_inhabited_6ab26fc7bc93
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:36:27.441094+00:00
-- url     : https://prove2.me/theorems/4df6be36-c4ad-5cae-b147-430abe9c87e3
-- title:
--   P2 M Ground Theory Heights  Heights Sec Rank Specialize hypotheses inhabited 6ab26fc7bc93: P2 M Ground Theory Heights  Heights Sec Rank Specialize hypotheses inhabited 6ab26fc7bc93
-- statement:
--   The P2 M Ground Theory Heights  Heights Sec Rank Specialize hypotheses inhabited 6ab26fc7bc93 construction uses the P2 M Ground Theory Heights  Heights Sec Rank Specialize hypotheses inhabited 6ab26fc7bc93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsSecRankSpecialize.lean#L22-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsSecRankSpecialize.lean#L22-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecRankSpecialize
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSectionVertical_hypotheses_inhabited_25f0794614ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_hypotheses_inhabited_b7e6b352f62b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSwap_hypotheses_inhabited_286c010aa601
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_hypotheses_inhabited_32f5e648d58c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightMul_hypotheses_inhabited_0cc03fe7f1d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightRecursion_hypotheses_inhabited_a59b12a05d49
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerMul_hypotheses_inhabited_95e2ae5d82a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerSection_hypotheses_inhabited_066629c10381
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanLinear_hypotheses_inhabited_1fdf021d66be

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

theorem P2M_GroundTheory_Heights__Heights_SecRankSpecialize_hypotheses_inhabited_6ab26fc7bc93 :
    letI : Algebra (PowerSeries ℚ) ℚ := (PowerSeries.constantCoeff (R := ℚ)).toAlgebra
    IsDomain (PowerSeries ℚ) ∧ IsLocalRing (PowerSeries ℚ) ∧
      IsFractionRing (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) ∧
      Function.Surjective (algebraMap (PowerSeries ℚ) ℚ) ∧
      Module.Finite (PowerSeries ℚ)
        (Vertical.SecAlg (⊥ : Ideal (MvPolynomial (Fin 1) (PowerSeries ℚ)))
          (fun _ : Vertical.Par 0 1 => (1 : PowerSeries ℚ))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SecRankSpecialize».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_SecRankSpecialize_hypotheses_inhabited_6ab26fc7bc93
