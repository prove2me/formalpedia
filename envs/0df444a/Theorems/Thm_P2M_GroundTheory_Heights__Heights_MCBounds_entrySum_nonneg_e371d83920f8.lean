-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_entrySum_nonneg_e371d83920f8
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_entrySum_nonneg_e371d83920f8
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:47.340311+00:00
-- url     : https://prove2.me/theorems/9c72d73b-98c3-4e6b-9d57-083d1610485a
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds entry Sum nonneg e371d83920f8: P2 M Ground Theory Heights  Heights MCBounds entry Sum nonneg e371d83920f8
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds entry Sum nonneg e371d83920f8 construction uses the P2 M Ground Theory Heights  Heights MCBounds entry Sum nonneg e371d83920f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L13-L14

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_entrySum_nonneg_e371d83920f8 {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : 0 ≤ entrySum A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«entrySum_nonneg» := P2M_GroundTheory_Heights__Heights_MCBounds_entrySum_nonneg_e371d83920f8
