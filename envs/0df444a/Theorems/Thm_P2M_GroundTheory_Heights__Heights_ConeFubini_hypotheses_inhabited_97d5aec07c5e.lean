-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFubini_hypotheses_inhabited_97d5aec07c5e
-- name    : P2M_GroundTheory_Heights__Heights_ConeFubini_hypotheses_inhabited_97d5aec07c5e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:02:58.060192+00:00
-- url     : https://prove2.me/theorems/674bf2eb-01e2-5cd5-b2fd-c740526a24e9
-- title:
--   P2 M Ground Theory Heights  Heights Cone Fubini hypotheses inhabited 97d5aec07c5e: P2 M Ground Theory Heights  Heights Cone Fubini hypotheses inhabited 97d5aec07c5e
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Fubini hypotheses inhabited 97d5aec07c5e construction uses the P2 M Ground Theory Heights  Heights Cone Fubini hypotheses inhabited 97d5aec07c5e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L377-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsMahler.lean#L377-L380

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormBaseChange_hypotheses_inhabited_d4e9bb785044
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSectionVertical_hypotheses_inhabited_25f0794614ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_hypotheses_inhabited_b7e6b352f62b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSwap_hypotheses_inhabited_286c010aa601
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_hypotheses_inhabited_32f5e648d58c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightMul_hypotheses_inhabited_0cc03fe7f1d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightRecursion_hypotheses_inhabited_a59b12a05d49
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeIntegralMass_hypotheses_inhabited_a1fb323fc42c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GreenSymmetry_hypotheses_inhabited_2fbf7471ddd6
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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ConeFubini_hypotheses_inhabited_97d5aec07c5e :
    IsFiniteMeasure (Measure.dirac (0 : EuclideanSpace ℂ (Fin 1))) ∧
      Measurable (Function.uncurry fun (_ : Fin 1 → ℂ) (_ : EuclideanSpace ℂ (Fin 1)) => (0 : ℝ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeFubini».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_ConeFubini_hypotheses_inhabited_97d5aec07c5e
