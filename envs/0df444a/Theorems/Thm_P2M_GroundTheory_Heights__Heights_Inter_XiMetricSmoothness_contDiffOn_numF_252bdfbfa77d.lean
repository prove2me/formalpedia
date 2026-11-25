-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_numF_252bdfbfa77d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_numF_252bdfbfa77d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:24.590597+00:00
-- url     : https://prove2.me/theorems/bcd628f0-75ce-4596-afe4-bb8f7c8fe605
-- title:
--   P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff On num F 252bdfbfa77d: P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff On num F 252bdfbfa77d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff On num F 252bdfbfa77d construction uses the P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness cont Diff On num F 252bdfbfa77d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L375-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L375-L382

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
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
variable {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : IsEEMetric G)
include hG

theorem P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_numF_252bdfbfa77d (F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (numF G F) (goodY ι ν κ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«XiMetricSmoothness».«contDiffOn_numF» := P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_numF_252bdfbfa77d
