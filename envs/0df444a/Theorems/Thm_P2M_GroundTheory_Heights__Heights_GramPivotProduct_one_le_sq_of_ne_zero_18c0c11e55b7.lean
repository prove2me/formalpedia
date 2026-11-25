-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GramPivotProduct_one_le_sq_of_ne_zero_18c0c11e55b7
-- name    : P2M_GroundTheory_Heights__Heights_GramPivotProduct_one_le_sq_of_ne_zero_18c0c11e55b7
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:26.731799+00:00
-- url     : https://prove2.me/theorems/cbf7563e-71fb-48f2-bc61-b67e746b64cf
-- title:
--   P2 M Ground Theory Heights  Heights Gram Pivot Product one le sq of ne zero 18c0c11e55b7: P2 M Ground Theory Heights  Heights Gram Pivot Product one le sq of ne zero 18c0c11e55b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Gram Pivot Product one le sq of ne zero 18c0c11e55b7 construction uses the P2 M Ground Theory Heights  Heights Gram Pivot Product one le sq of ne zero 18c0c11e55b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramPivotProduct.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramPivotProduct.lean#L36-L39

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

theorem P2M_GroundTheory_Heights__Heights_GramPivotProduct_one_le_sq_of_ne_zero_18c0c11e55b7 {n : ℤ} (hn : n ≠ 0) : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GramPivotProduct».«one_le_sq_of_ne_zero» := P2M_GroundTheory_Heights__Heights_GramPivotProduct_one_le_sq_of_ne_zero_18c0c11e55b7
