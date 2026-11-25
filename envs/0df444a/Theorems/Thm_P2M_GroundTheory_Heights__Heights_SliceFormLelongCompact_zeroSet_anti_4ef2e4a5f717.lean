-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_zeroSet_anti_4ef2e4a5f717
-- name    : P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_zeroSet_anti_4ef2e4a5f717
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:39:07.584226+00:00
-- url     : https://prove2.me/theorems/1aec560f-77c6-4c09-b892-2e0e36170e03
-- title:
--   P2 M Ground Theory Heights  Heights Slice Form Lelong Compact zero Set anti 4ef2e4a5f717: P2 M Ground Theory Heights  Heights Slice Form Lelong Compact zero Set anti 4ef2e4a5f717
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Form Lelong Compact zero Set anti 4ef2e4a5f717 construction uses the P2 M Ground Theory Heights  Heights Slice Form Lelong Compact zero Set anti 4ef2e4a5f717 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L28-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceFormLelongCompactLimit
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
open scoped ContDiff Manifold
noncomputable section
open GroundTheory.Heights₂.Heights.SliceFormLelongCompact
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_zeroSet_anti_4ef2e4a5f717 {I I' : Ideal (MvPolynomial (Fin n) ℂ)} (hle : I ≤ I') : zeroSet I' ⊆ zeroSet I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceFormLelongCompact».«zeroSet_anti» := P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_zeroSet_anti_4ef2e4a5f717
