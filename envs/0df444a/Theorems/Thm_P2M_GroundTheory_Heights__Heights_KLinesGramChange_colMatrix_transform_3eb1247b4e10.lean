-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGramChange_colMatrix_transform_3eb1247b4e10
-- name    : P2M_GroundTheory_Heights__Heights_KLinesGramChange_colMatrix_transform_3eb1247b4e10
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:54.944977+00:00
-- url     : https://prove2.me/theorems/912ca162-6e45-4368-8c6e-7d42746673c4
-- title:
--   P2 M Ground Theory Heights  Heights KLines Gram Change col Matrix transform 3eb1247b4e10: P2 M Ground Theory Heights  Heights KLines Gram Change col Matrix transform 3eb1247b4e10
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Gram Change col Matrix transform 3eb1247b4e10 construction uses the P2 M Ground Theory Heights  Heights KLines Gram Change col Matrix transform 3eb1247b4e10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGramChange.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGramChange.lean#L25-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGramChange
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
open Matrix
open GroundTheory.Heights₂.Heights.KLinesGramChange

theorem P2M_GroundTheory_Heights__Heights_KLinesGramChange_colMatrix_transform_3eb1247b4e10 {K : Type*} [Field K] {n : ℕ} (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    (u : ι → Fin n → K) (P : Matrix ι ι K) :
    colMatrix σ (fun a => ∑ b, P b a • u b) = colMatrix σ u * P.map σ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesGramChange».«colMatrix_transform» := P2M_GroundTheory_Heights__Heights_KLinesGramChange_colMatrix_transform_3eb1247b4e10
