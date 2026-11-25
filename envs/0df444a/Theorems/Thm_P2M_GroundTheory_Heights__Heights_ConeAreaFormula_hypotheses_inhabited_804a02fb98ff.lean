-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeAreaFormula_hypotheses_inhabited_804a02fb98ff
-- name    : P2M_GroundTheory_Heights__Heights_ConeAreaFormula_hypotheses_inhabited_804a02fb98ff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:20:41.004959+00:00
-- url     : https://prove2.me/theorems/a2a66a1d-164a-59e4-bd41-f3d420581ffe
-- title:
--   P2 M Ground Theory Heights  Heights Cone Area Formula hypotheses inhabited 804a02fb98ff: P2 M Ground Theory Heights  Heights Cone Area Formula hypotheses inhabited 804a02fb98ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Area Formula hypotheses inhabited 804a02fb98ff construction uses the P2 M Ground Theory Heights  Heights Cone Area Formula hypotheses inhabited 804a02fb98ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeTangentAverage.lean#L101-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeTangentAverage.lean#L101-L110

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AdmissibleAE_hypotheses_inhabited_d72f0e8aca3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowDegreePos_hypotheses_inhabited_7362a1aae6a4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormBaseChange_hypotheses_inhabited_d4e9bb785044
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSectionVertical_hypotheses_inhabited_25f0794614ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_hypotheses_inhabited_b7e6b352f62b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSwap_hypotheses_inhabited_286c010aa601
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_hypotheses_inhabited_32f5e648d58c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightMul_hypotheses_inhabited_0cc03fe7f1d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightRecursion_hypotheses_inhabited_a59b12a05d49
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFibreAverage_hypotheses_inhabited_8e8ca043c905
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFibreDegree_hypotheses_inhabited_7d66142c3999
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFubini_hypotheses_inhabited_97d5aec07c5e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeIntegralMass_hypotheses_inhabited_a1fb323fc42c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMassOfFibre_hypotheses_inhabited_77106a6e7ffc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DefectAverage_hypotheses_inhabited_f83caa6d54fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DefectSymm_hypotheses_inhabited_3f2a438095c0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FsLogAverage_hypotheses_inhabited_bd29e1850784
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GreenSymmetry_hypotheses_inhabited_2fbf7471ddd6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerMul_hypotheses_inhabited_95e2ae5d82a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerSection_hypotheses_inhabited_066629c10381
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointChowForm_hypotheses_inhabited_be7bb473e8ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProperSymm_hypotheses_inhabited_a36bc6ba1f9a
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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
variable {m n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ConeAreaFormula_hypotheses_inhabited_804a02fb98ff :
    IsProjPrime (coordPlaneIdeal 1 1) ∧ 0 < 1 ∧ 1 ≤ 1 + 1 ∧
      (∀ᵐ π : Fin 1 → Fin (1 + 1) → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 1),
        fibreCount (HermNorm.std (1 + 1)) (coordPlaneIdeal 1 1) π w ≠ ⊤) ∧
      Measurable (fun _ : EuclideanSpace ℂ (Fin 1) => (1 : ℝ≥0∞)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeAreaFormula».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_ConeAreaFormula_hypotheses_inhabited_804a02fb98ff
