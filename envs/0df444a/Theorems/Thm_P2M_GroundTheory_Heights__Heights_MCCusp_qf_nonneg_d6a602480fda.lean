-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_qf_nonneg_d6a602480fda
-- name    : P2M_GroundTheory_Heights__Heights_MCCusp_qf_nonneg_d6a602480fda
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:09.085226+00:00
-- url     : https://prove2.me/theorems/1ec7eae8-3f1e-4dc8-a162-6773276903a5
-- title:
--   P2 M Ground Theory Heights  Heights MCCusp qf nonneg d6a602480fda: P2 M Ground Theory Heights  Heights MCCusp qf nonneg d6a602480fda
-- statement:
--   The P2 M Ground Theory Heights  Heights MCCusp qf nonneg d6a602480fda construction uses the P2 M Ground Theory Heights  Heights MCCusp qf nonneg d6a602480fda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/TransposeEqOfPosSemidef.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/TransposeEqOfPosSemidef.lean#L23-L25

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

theorem P2M_GroundTheory_Heights__Heights_MCCusp_qf_nonneg_d6a602480fda {Z : Matrix ι ι ℝ} (hZ : Z.PosSemidef) (u : ι → ℝ) : 0 ≤ qf Z u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCCusp».«qf_nonneg» := P2M_GroundTheory_Heights__Heights_MCCusp_qf_nonneg_d6a602480fda
