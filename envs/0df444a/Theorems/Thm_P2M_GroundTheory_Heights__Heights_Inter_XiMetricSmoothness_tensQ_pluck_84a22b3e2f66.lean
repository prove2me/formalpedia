-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_tensQ_pluck_84a22b3e2f66
-- name    : P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_tensQ_pluck_84a22b3e2f66
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:52.72546+00:00
-- url     : https://prove2.me/theorems/86387406-dff4-48e1-b80c-fec947ae906f
-- title:
--   P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness tens Q pluck 84a22b3e2f66: P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness tens Q pluck 84a22b3e2f66
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness tens Q pluck 84a22b3e2f66 construction uses the P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness tens Q pluck 84a22b3e2f66 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L63-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L63-L77

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

theorem P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_tensQ_pluck_84a22b3e2f66 {G : Matrix κ κ ℂ} (hG : G.IsHermitian) (a b : κ → ℂ) :
    tensQ G (fun p => a p.1 * b p.2 - a p.2 * b p.1) =
      2 * ((hermG G a a).re * (hermG G b b).re - ‖hermG G a b‖ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«XiMetricSmoothness».«tensQ_pluck» := P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_tensQ_pluck_84a22b3e2f66
