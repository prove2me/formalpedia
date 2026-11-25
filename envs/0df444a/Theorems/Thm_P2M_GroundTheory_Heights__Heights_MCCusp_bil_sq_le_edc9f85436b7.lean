-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_bil_sq_le_edc9f85436b7
-- name    : P2M_GroundTheory_Heights__Heights_MCCusp_bil_sq_le_edc9f85436b7
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:30.654835+00:00
-- url     : https://prove2.me/theorems/ebd6c185-657f-4e52-acba-608f3d59a406
-- title:
--   P2 M Ground Theory Heights  Heights MCCusp bil sq le edc9f85436b7: P2 M Ground Theory Heights  Heights MCCusp bil sq le edc9f85436b7
-- statement:
--   The P2 M Ground Theory Heights  Heights MCCusp bil sq le edc9f85436b7 construction uses the P2 M Ground Theory Heights  Heights MCCusp bil sq le edc9f85436b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/TransposeEqOfPosSemidef.lean#L27-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/TransposeEqOfPosSemidef.lean#L27-L41

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

theorem P2M_GroundTheory_Heights__Heights_MCCusp_bil_sq_le_edc9f85436b7 {Z : Matrix ι ι ℝ} (hZ : Z.PosSemidef) (u w : ι → ℝ) :
    (w ⬝ᵥ (Z *ᵥ u)) ^ 2 ≤ qf Z w * qf Z u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCCusp».«bil_sq_le» := P2M_GroundTheory_Heights__Heights_MCCusp_bil_sq_le_edc9f85436b7
