-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualTopBound_proof_b50e4f0fa276
-- name    : P2M_GroundTheory_Heights__Heights_DualTopBound_proof_b50e4f0fa276
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:11:28.787047+00:00
-- url     : https://prove2.me/theorems/153fd8c0-679b-4dad-8616-ebbdfcbf6006
-- title:
--   P2 M Ground Theory Heights  Heights Dual Top Bound proof b50e4f0fa276: P2 M Ground Theory Heights  Heights Dual Top Bound proof b50e4f0fa276
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Top Bound proof b50e4f0fa276 construction uses the P2 M Ground Theory Heights  Heights Dual Top Bound proof b50e4f0fa276 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualTopBound.lean#L23-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualTopBound.lean#L23-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ScaledExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualTopBound
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
open ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_DualTopBound_proof_b50e4f0fa276 (hBasis : DualLatticeBasisExists.Statement)
    (hBij : DualEmbBijective.Statement) (hMetric : DualTopMetricChange.Statement)
    (hLattice : DualTopLatticeChange.Statement) (hStd : DualTopStandard.Statement)
    (hDeg : DualGeomDegStandard.Statement) (hGrass : GrassHeightBound.Statement) :
    DualTopBound.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualTopBound».«proof» := P2M_GroundTheory_Heights__Heights_DualTopBound_proof_b50e4f0fa276
