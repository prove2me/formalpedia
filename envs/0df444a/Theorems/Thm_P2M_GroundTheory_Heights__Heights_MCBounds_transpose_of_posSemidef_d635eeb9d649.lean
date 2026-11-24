-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_transpose_of_posSemidef_d635eeb9d649
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_transpose_of_posSemidef_d635eeb9d649
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:26.362675+00:00
-- url     : https://prove2.me/theorems/2a21d0b3-f692-4378-9c89-a1125204a80b
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds transpose of pos Semidef d635eeb9d649: P2 M Ground Theory Heights  Heights MCBounds transpose of pos Semidef d635eeb9d649
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds transpose of pos Semidef d635eeb9d649 construction uses the P2 M Ground Theory Heights  Heights MCBounds transpose of pos Semidef d635eeb9d649 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/BoundsY.lean#L66-L67

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_transpose_of_posSemidef_d635eeb9d649 {ι : Type*} {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : Aᵀ = A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«transpose_of_posSemidef» := P2M_GroundTheory_Heights__Heights_MCBounds_transpose_of_posSemidef_d635eeb9d649
