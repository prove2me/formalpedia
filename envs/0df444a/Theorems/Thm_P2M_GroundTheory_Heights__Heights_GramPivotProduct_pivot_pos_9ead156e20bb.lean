-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GramPivotProduct_pivot_pos_9ead156e20bb
-- name    : P2M_GroundTheory_Heights__Heights_GramPivotProduct_pivot_pos_9ead156e20bb
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:37.806545+00:00
-- url     : https://prove2.me/theorems/1660e2a3-843b-4b65-8ae2-6e9516637eb8
-- title:
--   P2 M Ground Theory Heights  Heights Gram Pivot Product pivot pos 9ead156e20bb: P2 M Ground Theory Heights  Heights Gram Pivot Product pivot pos 9ead156e20bb
-- statement:
--   The P2 M Ground Theory Heights  Heights Gram Pivot Product pivot pos 9ead156e20bb construction uses the P2 M Ground Theory Heights  Heights Gram Pivot Product pivot pos 9ead156e20bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramPivotProduct.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramPivotProduct.lean#L27-L30

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

theorem P2M_GroundTheory_Heights__Heights_GramPivotProduct_pivot_pos_9ead156e20bb (hLB : LeadMinorBasic.Statement) {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosDef) {i : ℕ} (hi : i < d) : 0 < pivot S i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GramPivotProduct».«pivot_pos» := P2M_GroundTheory_Heights__Heights_GramPivotProduct_pivot_pos_9ead156e20bb
