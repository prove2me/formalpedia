-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GramPivotProduct_intGram_transpose_79e03d83922d
-- name    : P2M_GroundTheory_Heights__Heights_GramPivotProduct_intGram_transpose_79e03d83922d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:11.445172+00:00
-- url     : https://prove2.me/theorems/49650fb3-1d54-48f2-bb0f-0f2577753479
-- title:
--   P2 M Ground Theory Heights  Heights Gram Pivot Product int Gram transpose 79e03d83922d: P2 M Ground Theory Heights  Heights Gram Pivot Product int Gram transpose 79e03d83922d
-- statement:
--   The P2 M Ground Theory Heights  Heights Gram Pivot Product int Gram transpose 79e03d83922d construction uses the P2 M Ground Theory Heights  Heights Gram Pivot Product int Gram transpose 79e03d83922d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramPivotProduct.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramPivotProduct.lean#L32-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PGramPivotProduct
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
noncomputable section
open GroundTheory.Heights₂.Heights.GramPivotProduct

theorem P2M_GroundTheory_Heights__Heights_GramPivotProduct_intGram_transpose_79e03d83922d {d k : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : Sᵀ = S)
    (N : Matrix (Fin d) (Fin k) ℤ) : (intGram S N)ᵀ = intGram S N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GramPivotProduct».«intGram_transpose» := P2M_GroundTheory_Heights__Heights_GramPivotProduct_intGram_transpose_79e03d83922d
