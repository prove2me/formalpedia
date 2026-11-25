-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GramPivotProduct_pivot_submatrix_7b75b2f54d37
-- name    : P2M_GroundTheory_Heights__Heights_GramPivotProduct_pivot_submatrix_7b75b2f54d37
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:35.052078+00:00
-- url     : https://prove2.me/theorems/93b12206-0e50-4d34-ae97-3d72b8b7c4ba
-- title:
--   P2 M Ground Theory Heights  Heights Gram Pivot Product pivot submatrix 7b75b2f54d37: P2 M Ground Theory Heights  Heights Gram Pivot Product pivot submatrix 7b75b2f54d37
-- statement:
--   The P2 M Ground Theory Heights  Heights Gram Pivot Product pivot submatrix 7b75b2f54d37 construction uses the P2 M Ground Theory Heights  Heights Gram Pivot Product pivot submatrix 7b75b2f54d37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramPivotProduct.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramPivotProduct.lean#L20-L25

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

theorem P2M_GroundTheory_Heights__Heights_GramPivotProduct_pivot_submatrix_7b75b2f54d37 (hLL : LeadMinorLeading.Statement) {d : ℕ}
    (S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) {i : ℕ} (hi : i < d) :
    pivot (S.submatrix Fin.castSucc Fin.castSucc) i = pivot S i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GramPivotProduct».«pivot_submatrix» := P2M_GroundTheory_Heights__Heights_GramPivotProduct_pivot_submatrix_7b75b2f54d37
