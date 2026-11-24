-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_posDef_of_ge_c2392ab1fa43
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_posDef_of_ge_c2392ab1fa43
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:20.37474+00:00
-- url     : https://prove2.me/theorems/c9c200ff-da37-477b-bfcb-7533071611ab
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds pos Def of ge c2392ab1fa43: P2 M Ground Theory Heights  Heights MCBounds pos Def of ge c2392ab1fa43
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds pos Def of ge c2392ab1fa43 construction uses the P2 M Ground Theory Heights  Heights MCBounds pos Def of ge c2392ab1fa43 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L87-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L87-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_MCBounds_posDef_of_ge_c2392ab1fa43 {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (h : (A - c • (1 : Matrix ι ι ℝ)).PosSemidef) : A.PosDef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«posDef_of_ge» := P2M_GroundTheory_Heights__Heights_MCBounds_posDef_of_ge_c2392ab1fa43
