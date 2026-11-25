-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_matGauss_eq_prod_1daa5cb7a9a6
-- name    : P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_matGauss_eq_prod_1daa5cb7a9a6
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:03.579411+00:00
-- url     : https://prove2.me/theorems/e41bad31-f2b2-47af-9aec-a79a4aeb6296
-- title:
--   P2 M Ground Theory Heights  Heights Lead Block Gauss Tail mat Gauss eq prod 1daa5cb7a9a6: P2 M Ground Theory Heights  Heights Lead Block Gauss Tail mat Gauss eq prod 1daa5cb7a9a6
-- statement:
--   The P2 M Ground Theory Heights  Heights Lead Block Gauss Tail mat Gauss eq prod 1daa5cb7a9a6 construction uses the P2 M Ground Theory Heights  Heights Lead Block Gauss Tail mat Gauss eq prod 1daa5cb7a9a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L202-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L202-L209

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail
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
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail

theorem P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_matGauss_eq_prod_1daa5cb7a9a6 {m n : ℕ} (π : Fin m → Fin n → ℂ) :
    matGauss π = ∏ i, ∏ j, ENNReal.ofReal (Real.exp (-‖π i j‖ ^ 2)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LeadBlockGaussTail».«matGauss_eq_prod» := P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_matGauss_eq_prod_1daa5cb7a9a6
