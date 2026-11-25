-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_succ_le_of_ringKrullDim_quotient_fb5ca6b44376
-- name    : P2M_GroundTheory_Heights__Heights_succ_le_of_ringKrullDim_quotient_fb5ca6b44376
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:51:28.490818+00:00
-- url     : https://prove2.me/theorems/c81cb099-e8b7-4975-9bb6-257f4d393cb6
-- title:
--   P2 M Ground Theory Heights  Heights succ le of ring Krull Dim quotient fb5ca6b44376: P2 M Ground Theory Heights  Heights succ le of ring Krull Dim quotient fb5ca6b44376
-- statement:
--   The P2 M Ground Theory Heights  Heights succ le of ring Krull Dim quotient fb5ca6b44376 construction uses the P2 M Ground Theory Heights  Heights succ le of ring Krull Dim quotient fb5ca6b44376 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeSheetGram.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeSheetGram.lean#L22-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGramLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeSheetGram
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
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_succ_le_of_ringKrullDim_quotient_fb5ca6b44376 {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞)) : e + 1 ≤ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«succ_le_of_ringKrullDim_quotient» := P2M_GroundTheory_Heights__Heights_succ_le_of_ringKrullDim_quotient_fb5ca6b44376
