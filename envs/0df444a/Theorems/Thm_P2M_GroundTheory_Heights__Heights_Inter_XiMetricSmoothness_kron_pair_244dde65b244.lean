-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_kron_pair_244dde65b244
-- name    : P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_kron_pair_244dde65b244
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:33:40.315399+00:00
-- url     : https://prove2.me/theorems/ce5eba27-f8b1-5887-8815-2bd91b790b4d
-- title:
--   P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness kron pair 244dde65b244: P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness kron pair 244dde65b244
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness kron pair 244dde65b244 construction uses the P2 M Ground Theory Heights  Heights Inter Xi Metric Smoothness kron pair 244dde65b244 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L41-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean#L41-L56

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

theorem P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_kron_pair_244dde65b244 (G : Matrix κ κ ℂ) (a b c d : κ → ℂ) :
    star (fun p : κ × κ => a p.1 * b p.2) ⬝ᵥ (Matrix.kronecker G G *ᵥ fun p => c p.1 * d p.2) =
      hermG G a c * hermG G b d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«XiMetricSmoothness».«kron_pair» := P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_kron_pair_244dde65b244
