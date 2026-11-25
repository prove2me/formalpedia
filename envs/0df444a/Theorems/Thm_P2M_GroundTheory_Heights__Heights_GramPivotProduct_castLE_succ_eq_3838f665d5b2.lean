-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GramPivotProduct_castLE_succ_eq_3838f665d5b2
-- name    : P2M_GroundTheory_Heights__Heights_GramPivotProduct_castLE_succ_eq_3838f665d5b2
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:21.830542+00:00
-- url     : https://prove2.me/theorems/2278c8c0-896e-4a9c-8187-a9233f4fe33c
-- title:
--   P2 M Ground Theory Heights  Heights Gram Pivot Product cast LE succ eq 3838f665d5b2: P2 M Ground Theory Heights  Heights Gram Pivot Product cast LE succ eq 3838f665d5b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Gram Pivot Product cast LE succ eq 3838f665d5b2 construction uses the P2 M Ground Theory Heights  Heights Gram Pivot Product cast LE succ eq 3838f665d5b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramPivotProduct.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PGramPivotProduct.lean#L15-L18

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

theorem P2M_GroundTheory_Heights__Heights_GramPivotProduct_castLE_succ_eq_3838f665d5b2 (d : ℕ) :
    (Fin.castLE (Nat.le_succ d) : Fin d → Fin (d + 1)) = Fin.castSucc := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GramPivotProduct».«castLE_succ_eq» := P2M_GroundTheory_Heights__Heights_GramPivotProduct_castLE_succ_eq_3838f665d5b2
