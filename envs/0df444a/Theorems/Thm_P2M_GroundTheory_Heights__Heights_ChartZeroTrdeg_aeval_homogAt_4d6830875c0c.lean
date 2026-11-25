-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartZeroTrdeg_aeval_homogAt_4d6830875c0c
-- name    : P2M_GroundTheory_Heights__Heights_ChartZeroTrdeg_aeval_homogAt_4d6830875c0c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:18:53.071054+00:00
-- url     : https://prove2.me/theorems/f6174c8b-269c-4001-b49f-53bc87e322e1
-- title:
--   P2 M Ground Theory Heights  Heights Chart Zero Trdeg aeval homog At 4d6830875c0c: P2 M Ground Theory Heights  Heights Chart Zero Trdeg aeval homog At 4d6830875c0c
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Zero Trdeg aeval homog At 4d6830875c0c construction uses the P2 M Ground Theory Heights  Heights Chart Zero Trdeg aeval homog At 4d6830875c0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartZeroTrdeg.lean#L19-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartZeroTrdeg.lean#L19-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartZeroTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartZeroTrdeg
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
open GroundTheory.Heights₂.Heights.ChartZeroTrdeg
variable {F : Type} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartZeroTrdeg_aeval_homogAt_4d6830875c0c {L : Type} [Field L] [Algebra F L] (p : MvPolynomial (Fin n) F) (j : Fin n)
    (N : ℕ) (hN : p.totalDegree ≤ N) (z : Fin n → L) (hz : z j ≠ 0) :
    aeval z (homogAt p j N) = z j ^ N * aeval (fun m => z m * (z j)⁻¹) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartZeroTrdeg».«aeval_homogAt» := P2M_GroundTheory_Heights__Heights_ChartZeroTrdeg_aeval_homogAt_4d6830875c0c
