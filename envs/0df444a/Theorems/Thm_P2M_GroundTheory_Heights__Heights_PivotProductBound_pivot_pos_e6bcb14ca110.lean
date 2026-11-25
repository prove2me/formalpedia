-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PivotProductBound_pivot_pos_e6bcb14ca110
-- name    : P2M_GroundTheory_Heights__Heights_PivotProductBound_pivot_pos_e6bcb14ca110
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:26.138819+00:00
-- url     : https://prove2.me/theorems/79ec4f3b-ff79-4cdc-821c-4cfb835613b3
-- title:
--   P2 M Ground Theory Heights  Heights Pivot Product Bound pivot pos e6bcb14ca110: P2 M Ground Theory Heights  Heights Pivot Product Bound pivot pos e6bcb14ca110
-- statement:
--   The P2 M Ground Theory Heights  Heights Pivot Product Bound pivot pos e6bcb14ca110 construction uses the P2 M Ground Theory Heights  Heights Pivot Product Bound pivot pos e6bcb14ca110 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPivotProductBound.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PPivotProductBound.lean#L15-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPivotProductBound
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
open GroundTheory.Heights₂.Heights.PivotProductBound

theorem P2M_GroundTheory_Heights__Heights_PivotProductBound_pivot_pos_e6bcb14ca110 (hLB : LeadMinorBasic.Statement) {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosDef) {i : ℕ} (hi : i < d) : 0 < pivot S i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PivotProductBound».«pivot_pos» := P2M_GroundTheory_Heights__Heights_PivotProductBound_pivot_pos_e6bcb14ca110
