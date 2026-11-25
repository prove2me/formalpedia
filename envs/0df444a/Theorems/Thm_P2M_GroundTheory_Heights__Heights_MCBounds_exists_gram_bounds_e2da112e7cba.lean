-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_exists_gram_bounds_e2da112e7cba
-- name    : P2M_GroundTheory_Heights__Heights_MCBounds_exists_gram_bounds_e2da112e7cba
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:59.536121+00:00
-- url     : https://prove2.me/theorems/51e51311-6008-4e1c-8274-4168b876dae4
-- title:
--   P2 M Ground Theory Heights  Heights MCBounds exists gram bounds e2da112e7cba: P2 M Ground Theory Heights  Heights MCBounds exists gram bounds e2da112e7cba
-- statement:
--   The P2 M Ground Theory Heights  Heights MCBounds exists gram bounds e2da112e7cba construction uses the P2 M Ground Theory Heights  Heights MCBounds exists gram bounds e2da112e7cba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L145-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Bounds.lean#L145-L160

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

theorem P2M_GroundTheory_Heights__Heights_MCBounds_exists_gram_bounds_e2da112e7cba : ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧ ∀ p ∈ D.K,
    δ ≤ ((D.f p)ᴴ * D.f p).det.re ∧ ((D.f p)ᴴ * D.f p).det.re ≤ M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCBounds».«exists_gram_bounds» := P2M_GroundTheory_Heights__Heights_MCBounds_exists_gram_bounds_e2da112e7cba
