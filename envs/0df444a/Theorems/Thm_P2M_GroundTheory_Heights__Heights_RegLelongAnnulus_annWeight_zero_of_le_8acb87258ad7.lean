-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_annWeight_zero_of_le_8acb87258ad7
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_annWeight_zero_of_le_8acb87258ad7
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:20.230454+00:00
-- url     : https://prove2.me/theorems/872b70d8-cb66-4a17-9124-ead5483f21ac
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus ann Weight zero of le 8acb87258ad7: P2 M Ground Theory Heights  Heights Reg Lelong Annulus ann Weight zero of le 8acb87258ad7
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus ann Weight zero of le 8acb87258ad7 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus ann Weight zero of le 8acb87258ad7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L449-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L449-L456

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_annWeight_zero_of_le_8acb87258ad7 (hr : 0 < r) (hrs : r ≤ s) (k : ℕ) {t : ℝ} (ht : s ^ 2 ≤ t) :
    annWeight r s e k t = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«annWeight_zero_of_le» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_annWeight_zero_of_le_8acb87258ad7
