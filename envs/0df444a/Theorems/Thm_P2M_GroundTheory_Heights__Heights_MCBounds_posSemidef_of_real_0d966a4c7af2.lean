-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_posSemidef_of_real_0d966a4c7af2
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_posSemidef_of_real_0d966a4c7af2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:27.262643+00:00
-- url     : https://prove2.me/theorems/582b1246-5e29-443a-ae6b-1140fcfa9a47
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds pos Semidef of real 0d966a4c7af2: P2 M Ground Theory Heights  Heights MCBounds pos Semidef of real 0d966a4c7af2
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds pos Semidef of real 0d966a4c7af2 construction uses the P2 M Ground Theory Heights  Heights MCBounds pos Semidef of real 0d966a4c7af2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L57-L60

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_posSemidef_of_real_0d966a4c7af2 {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hs : Aᵀ = A)
    (h : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x)) : A.PosSemidef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«posSemidef_of_real» := P2M_GroundTheory_Heights__Heights_MCBounds_posSemidef_of_real_0d966a4c7af2
