-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_annWeight_const_bf676f231701
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_annWeight_const_bf676f231701
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:17:22.580817+00:00
-- url     : https://prove2.me/theorems/cc327cb8-b43a-4a03-963d-2e086b19de83
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus ann Weight const bf676f231701: P2 M Ground Theory Heights  Heights Reg Lelong Annulus ann Weight const bf676f231701
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus ann Weight const bf676f231701 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus ann Weight const bf676f231701 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L458-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L458-L466

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
variable {r s : ℝ} (e : ℕ)

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_annWeight_const_bf676f231701 (hr : 0 < r) (hrs : r ≤ s) (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 (pk k * r ^ 2)) :
    annWeight r s e k t = annWeight r s e k 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«annWeight_const» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_annWeight_const_bf676f231701
