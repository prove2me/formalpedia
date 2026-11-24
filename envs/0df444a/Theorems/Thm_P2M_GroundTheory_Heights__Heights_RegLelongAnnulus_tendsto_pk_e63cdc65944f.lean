-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_pk_e63cdc65944f
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_pk_e63cdc65944f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:04.666463+00:00
-- url     : https://prove2.me/theorems/aead0d10-102f-4901-8379-c17dd42aab02
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto pk e63cdc65944f: P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto pk e63cdc65944f
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto pk e63cdc65944f construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto pk e63cdc65944f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L215-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L215-L219

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_pk_e63cdc65944f : Tendsto pk atTop (𝓝 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«tendsto_pk» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_pk_e63cdc65944f
