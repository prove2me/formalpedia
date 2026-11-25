-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_injective_of_rank_3ea88de2b0c7
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_injective_of_rank_3ea88de2b0c7
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:43.645429+00:00
-- url     : https://prove2.me/theorems/5469fac1-cef4-4e6d-940c-dabd8de17cf4
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds injective of rank 3ea88de2b0c7: P2 M Ground Theory Heights  Heights MCBounds injective of rank 3ea88de2b0c7
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds injective of rank 3ea88de2b0c7 construction uses the P2 M Ground Theory Heights  Heights MCBounds injective of rank 3ea88de2b0c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L128-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L128-L135

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
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
open scoped ComplexOrder
noncomputable section
variable (D : PeriodChartData)

theorem P2M_GroundTheory_Heights__Heights_MCBounds_injective_of_rank_3ea88de2b0c7 {g rk : ℕ} (F : Matrix (Fin g) (Fin rk) ℂ) (h : F.rank = rk) :
    Function.Injective F.mulVec := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«injective_of_rank» := P2M_GroundTheory_Heights__Heights_MCBounds_injective_of_rank_3ea88de2b0c7
