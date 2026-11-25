-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_hermG_swap_34994cfc3a37
-- name    : P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_hermG_swap_34994cfc3a37
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:35.536835+00:00
-- url     : https://prove2.me/theorems/efaa939b-cf78-40c9-9ea1-9488333637e4
-- title:
--   P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness herm G swap 34994cfc3a37: P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness herm G swap 34994cfc3a37
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness herm G swap 34994cfc3a37 construction uses the P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness herm G swap 34994cfc3a37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L58-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open scoped ComplexOrder
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
variable {κ : Type} [Fintype κ]

theorem P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_hermG_swap_34994cfc3a37 {G : Matrix κ κ ℂ} (hG : G.IsHermitian) (a b : κ → ℂ) :
    hermG G b a = star (hermG G a b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«XiMetricSmoothness».«hermG_swap» := P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_hermG_swap_34994cfc3a37
