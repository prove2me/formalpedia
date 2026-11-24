-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_transpose_eq_of_posSemidef_d388a88d8b69
-- name    : P2M_GroundTheory_Heights__Heights_MCCusp_transpose_eq_of_posSemidef_d388a88d8b69
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:02.735587+00:00
-- url     : https://prove2.me/theorems/bc155b2f-845d-462d-be91-29fe011f14a6
-- title:
--   P2 M Ground Theory Heights  Heights MCCusp transpose eq of pos Semidef d388a88d8b69: P2 M Ground Theory Heights  Heights MCCusp transpose eq of pos Semidef d388a88d8b69
-- statement:
--   The P2 M Ground Theory Heights  Heights MCCusp transpose eq of pos Semidef d388a88d8b69 construction uses the P2 M Ground Theory Heights  Heights MCCusp transpose eq of pos Semidef d388a88d8b69 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/TransposeEqOfPosSemidef.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/TransposeEqOfPosSemidef.lean#L19-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_HermValueIsLeast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCCusp
open Matrix GroundTheory.Heights₂.Heights.MCSchur
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_MCCusp_transpose_eq_of_posSemidef_d388a88d8b69 {Z : Matrix ι ι ℝ} (hZ : Z.PosSemidef) : Zᵀ = Z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCCusp».«transpose_eq_of_posSemidef» := P2M_GroundTheory_Heights__Heights_MCCusp_transpose_eq_of_posSemidef_d388a88d8b69
