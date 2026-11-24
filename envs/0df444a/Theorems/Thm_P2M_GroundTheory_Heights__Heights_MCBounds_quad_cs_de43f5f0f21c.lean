-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_quad_cs_de43f5f0f21c
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_quad_cs_de43f5f0f21c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:20.412227+00:00
-- url     : https://prove2.me/theorems/637a0313-96ca-4ede-965e-a4b1dc065c38
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds quad cs de43f5f0f21c: P2 M Ground Theory Heights  Heights MCBounds quad cs de43f5f0f21c
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds quad cs de43f5f0f21c construction uses the P2 M Ground Theory Heights  Heights MCBounds quad cs de43f5f0f21c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L73-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L73-L85

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_quad_cs_de43f5f0f21c {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (u v : ι → ℝ) :
    (u ⬝ᵥ (A *ᵥ v)) ^ 2 ≤ (u ⬝ᵥ (A *ᵥ u)) * (v ⬝ᵥ (A *ᵥ v)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«quad_cs» := P2M_GroundTheory_Heights__Heights_MCBounds_quad_cs_de43f5f0f21c
