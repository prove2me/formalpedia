-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepTwo_Reduce_proof_d427b891ed9f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepTwo_Reduce_proof_d427b891ed9f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:28:33.012013+00:00
-- url     : https://prove2.me/theorems/02888761-1b9f-488e-a410-98e3f7dff0cf
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Two Reduce proof d427b891ed9f: P2 M Ground Theory Heights  Heights Kleiman Step Two Reduce proof d427b891ed9f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Two Reduce proof d427b891ed9f construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Two Reduce proof d427b891ed9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepTwoReduce.lean#L55-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepTwoReduce.lean#L55-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotTransSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoPieceSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepTwoReduce
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepTwo_Reduce_proof_d427b891ed9f (hF : StepTwo.Filt.Statement.{u, v, w}) (hT : QuotTrans.Statement.{u, v, w})
    (hP : StepTwo.Piece.Statement.{u, v, w}) : StepTwo.Reduce.Statement.{u, v, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepTwo».«Reduce».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_StepTwo_Reduce_proof_d427b891ed9f
