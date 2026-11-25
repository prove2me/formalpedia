-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeomDegCharts_proof_d873f9307c28
-- name    : P2M_GroundTheory_Heights__Heights_DualGeomDegCharts_proof_d873f9307c28
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:27.046933+00:00
-- url     : https://prove2.me/theorems/3f34a9ac-5b1d-5a30-94b6-75a8e499d8e9
-- title:
--   P2 M Ground Theory Heights  Heights Dual Geom Deg Charts proof d873f9307c28: P2 M Ground Theory Heights  Heights Dual Geom Deg Charts proof d873f9307c28
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Geom Deg Charts proof d873f9307c28 construction uses the P2 M Ground Theory Heights  Heights Dual Geom Deg Charts proof d873f9307c28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegCharts.lean#L256-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegCharts.lean#L256-L266

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualGeomDegCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOfPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPtsOfPlane_proof_4394ca2b9395
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPtsOnPlane_proof_e41a18cf842f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualStdMassAt_proof_fd101889fa59

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
open ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter Topology Matrix NumberField
open scoped ComplexOrder
noncomputable section
open DualGeometricDegreeCharts

theorem P2M_GroundTheory_Heights__Heights_DualGeomDegCharts_proof_d873f9307c28 (hInt : ChartDensityIntegrable.Statement) : DualGeomDegCharts.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualGeomDegCharts».«proof» := P2M_GroundTheory_Heights__Heights_DualGeomDegCharts_proof_d873f9307c28
