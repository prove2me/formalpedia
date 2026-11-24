-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_nonneg_28912038225c
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_quad_nonneg_28912038225c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:57.698849+00:00
-- url     : https://prove2.me/theorems/f42f3578-e144-40c4-bb88-ac86b24c97f6
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds quad nonneg 28912038225c: P2 M Ground Theory Heights  Heights MCBounds quad nonneg 28912038225c
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds quad nonneg 28912038225c construction uses the P2 M Ground Theory Heights  Heights MCBounds quad nonneg 28912038225c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L62-L64

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_quad_nonneg_28912038225c {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (x : ι → ℝ) : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«quad_nonneg» := P2M_GroundTheory_Heights__Heights_MCBounds_quad_nonneg_28912038225c
