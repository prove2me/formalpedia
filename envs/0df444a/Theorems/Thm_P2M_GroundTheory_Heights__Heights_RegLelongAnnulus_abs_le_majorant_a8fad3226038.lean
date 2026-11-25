-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_le_majorant_a8fad3226038
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_le_majorant_a8fad3226038
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:17:31.850805+00:00
-- url     : https://prove2.me/theorems/0d4b15d6-49c2-4b51-9ab1-26296db9a631
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus abs le majorant a8fad3226038: P2 M Ground Theory Heights  Heights Reg Lelong Annulus abs le majorant a8fad3226038
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus abs le majorant a8fad3226038 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus abs le majorant a8fad3226038 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L378-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L378-L384

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegLelongAnnulus
variable {n : ℕ} (x : Fin n → ℂ)

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_le_majorant_a8fad3226038 {s C : ℝ} (hC : 0 ≤ C) {w : (Fin n → ℂ) → ℝ} (hw : ∀ z, |w z| ≤ C)
    (h0 : ∀ z, s ^ 2 ≤ euclPot (z - x) → w z = 0) (z : Fin n → ℂ) : |w z| ≤ C * majorant x s z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«abs_le_majorant» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_le_majorant_a8fad3226038
