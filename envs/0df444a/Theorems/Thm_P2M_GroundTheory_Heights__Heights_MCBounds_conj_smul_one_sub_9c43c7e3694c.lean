-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_conj_smul_one_sub_9c43c7e3694c
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_conj_smul_one_sub_9c43c7e3694c
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:38.939125+00:00
-- url     : https://prove2.me/theorems/609273ad-f8e9-4e32-a672-e3238759b6f3
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds conj smul one sub 9c43c7e3694c: P2 M Ground Theory Heights  Heights MCBounds conj smul one sub 9c43c7e3694c
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds conj smul one sub 9c43c7e3694c construction uses the P2 M Ground Theory Heights  Heights MCBounds conj smul one sub 9c43c7e3694c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartBounds.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PChartBounds.lean#L27-L30

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_conj_smul_one_sub_9c43c7e3694c {g k : ℕ} (F : Matrix (Fin g) (Fin k) ℂ) (s : ℂ)
    (Z : Matrix (Fin g) (Fin g) ℂ) :
    Fᴴ * (s • (1 : Matrix (Fin g) (Fin g) ℂ) - Z) * F = s • (Fᴴ * F) - Fᴴ * Z * F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«conj_smul_one_sub» := P2M_GroundTheory_Heights__Heights_MCBounds_conj_smul_one_sub_9c43c7e3694c
