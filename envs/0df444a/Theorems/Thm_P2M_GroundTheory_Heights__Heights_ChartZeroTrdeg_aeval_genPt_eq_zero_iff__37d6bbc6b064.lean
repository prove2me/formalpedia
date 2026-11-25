-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartZeroTrdeg_aeval_genPt_eq_zero_iff__37d6bbc6b064
-- name    : P2M_GroundTheory_Heights__Heights_ChartZeroTrdeg_aeval_genPt_eq_zero_iff__37d6bbc6b064
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:19:00.652912+00:00
-- url     : https://prove2.me/theorems/76fada08-4530-4abc-9dd0-f9287565740d
-- title:
--   P2 M Ground Theory Heights  Heights Chart Zero Trdeg aeval gen Pt eq zero iff  37d6bbc6b064: P2 M Ground Theory Heights  Heights Chart Zero Trdeg aeval gen Pt eq zero iff  37d6bbc6b064
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Zero Trdeg aeval gen Pt eq zero iff  37d6bbc6b064 construction uses the P2 M Ground Theory Heights  Heights Chart Zero Trdeg aeval gen Pt eq zero iff  37d6bbc6b064 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartZeroTrdeg.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartZeroTrdeg.lean#L36-L43

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

theorem P2M_GroundTheory_Heights__Heights_ChartZeroTrdeg_aeval_genPt_eq_zero_iff__37d6bbc6b064 (P : Ideal (MvPolynomial (Fin n) F)) (f : MvPolynomial (Fin n) F) :
    aeval (genPt P) f = 0 ↔ f ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartZeroTrdeg».«aeval_genPt_eq_zero_iff'» := P2M_GroundTheory_Heights__Heights_ChartZeroTrdeg_aeval_genPt_eq_zero_iff__37d6bbc6b064
