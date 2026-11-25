-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_Ik_fc9667f8e9a2
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_Ik_fc9667f8e9a2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:50.596844+00:00
-- url     : https://prove2.me/theorems/b7197cd8-39e5-46ad-b027-a231fcb0ef5b
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto Ik fc9667f8e9a2: P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto Ik fc9667f8e9a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto Ik fc9667f8e9a2 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto Ik fc9667f8e9a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L314-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L314-L317

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_Ik_fc9667f8e9a2 (e : ℕ) : Tendsto (Ik e) atTop (𝓝 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«tendsto_Ik» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_Ik_fc9667f8e9a2
