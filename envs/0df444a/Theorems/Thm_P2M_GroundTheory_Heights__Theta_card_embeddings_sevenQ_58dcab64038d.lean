-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_card_embeddings_sevenQ_58dcab64038d
-- name    : P2M_GroundTheory_Heights__Theta_card_embeddings_sevenQ_58dcab64038d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:53:27.733335+00:00
-- url     : https://prove2.me/theorems/d3860667-41c8-4460-848e-7db57459a796
-- title:
--   P2 M Ground Theory Heights  Theta card embeddings seven Q 58dcab64038d: P2 M Ground Theory Heights  Theta card embeddings seven Q 58dcab64038d
-- statement:
--   The P2 M Ground Theory Heights  Theta card embeddings seven Q 58dcab64038d construction uses the P2 M Ground Theory Heights  Theta card embeddings seven Q 58dcab64038d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/QuadraticFieldSqrtNegSeven.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/QuadraticFieldSqrtNegSeven.lean#L41-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_QuadraticFieldSqrtNegSeven
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField

theorem P2M_GroundTheory_Heights__Theta_card_embeddings_sevenQ_58dcab64038d : Fintype.card (QuadraticFieldSqrtNegSeven →+* ℂ) = 2 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«card_embeddings_sevenQ» := P2M_GroundTheory_Heights__Theta_card_embeddings_sevenQ_58dcab64038d
