-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_conj_sub_smul_one_f43216f942b1
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_conj_sub_smul_one_f43216f942b1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:04.263802+00:00
-- url     : https://prove2.me/theorems/773c44d4-3372-4dda-b47e-675ca1bb29e1
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds conj sub smul one f43216f942b1: P2 M Ground Theory Heights  Heights MCBounds conj sub smul one f43216f942b1
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds conj sub smul one f43216f942b1 construction uses the P2 M Ground Theory Heights  Heights MCBounds conj sub smul one f43216f942b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartBounds.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartBounds.lean#L32-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds
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
open Matrix MCBounds
open scoped ComplexOrder
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_MCBounds_conj_sub_smul_one_f43216f942b1 {g k : ℕ} (F : Matrix (Fin g) (Fin k) ℂ) (s : ℂ)
    (Z : Matrix (Fin g) (Fin g) ℂ) :
    Fᴴ * (Z - s • (1 : Matrix (Fin g) (Fin g) ℂ)) * F = Fᴴ * Z * F - s • (Fᴴ * F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«conj_sub_smul_one» := P2M_GroundTheory_Heights__Heights_MCBounds_conj_sub_smul_one_f43216f942b1
