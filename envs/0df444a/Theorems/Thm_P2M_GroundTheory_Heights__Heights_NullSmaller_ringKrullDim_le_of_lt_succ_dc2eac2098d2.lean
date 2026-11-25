-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NullSmaller_ringKrullDim_le_of_lt_succ_dc2eac2098d2
-- name    : P2M_GroundTheory_Heights__Heights_NullSmaller_ringKrullDim_le_of_lt_succ_dc2eac2098d2
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:23.30258+00:00
-- url     : https://prove2.me/theorems/a02f9cc6-1659-4869-b0a0-ea92845e344b
-- title:
--   P2 M Ground Theory Heights  Heights Null Smaller ring Krull Dim le of lt succ dc2eac2098d2: P2 M Ground Theory Heights  Heights Null Smaller ring Krull Dim le of lt succ dc2eac2098d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Null Smaller ring Krull Dim le of lt succ dc2eac2098d2 construction uses the P2 M Ground Theory Heights  Heights Null Smaller ring Krull Dim le of lt succ dc2eac2098d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNullSmaller.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNullSmaller.lean#L20-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PZeroLocusDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
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
open MvPolynomial MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NullSmaller_ringKrullDim_le_of_lt_succ_dc2eac2098d2 {R : Type*} [CommRing R] {k : ℕ}
    (h : ringKrullDim R < ((k + 1 : ℕ) : WithBot ℕ∞)) : ringKrullDim R ≤ (k : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NullSmaller».«ringKrullDim_le_of_lt_succ» := P2M_GroundTheory_Heights__Heights_NullSmaller_ringKrullDim_le_of_lt_succ_dc2eac2098d2
