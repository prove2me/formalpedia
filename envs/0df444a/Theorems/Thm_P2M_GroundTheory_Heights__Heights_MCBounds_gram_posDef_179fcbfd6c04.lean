-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_gram_posDef_179fcbfd6c04
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_gram_posDef_179fcbfd6c04
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:16.371971+00:00
-- url     : https://prove2.me/theorems/5279c5e0-ea6c-4d16-a663-2cfd552f27b6
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds gram pos Def 179fcbfd6c04: P2 M Ground Theory Heights  Heights MCBounds gram pos Def 179fcbfd6c04
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds gram pos Def 179fcbfd6c04 construction uses the P2 M Ground Theory Heights  Heights MCBounds gram pos Def 179fcbfd6c04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L137-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L137-L139

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_gram_posDef_179fcbfd6c04 {g rk : ℕ} (F : Matrix (Fin g) (Fin rk) ℂ) (h : F.rank = rk) :
    (Fᴴ * F).PosDef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«gram_posDef» := P2M_GroundTheory_Heights__Heights_MCBounds_gram_posDef_179fcbfd6c04
