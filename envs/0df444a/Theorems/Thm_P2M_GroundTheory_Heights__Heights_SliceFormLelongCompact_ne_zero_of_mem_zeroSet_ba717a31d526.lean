-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_ne_zero_of_mem_zeroSet_ba717a31d526
-- name    : P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_ne_zero_of_mem_zeroSet_ba717a31d526
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:08.377103+00:00
-- url     : https://prove2.me/theorems/6e39f00e-e54f-4eca-8ec3-c9274df42c02
-- title:
--   P2 M Ground Theory Heights  Heights Slice Form Lelong Compact ne zero of mem zero Set ba717a31d526: P2 M Ground Theory Heights  Heights Slice Form Lelong Compact ne zero of mem zero Set ba717a31d526
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Form Lelong Compact ne zero of mem zero Set ba717a31d526 construction uses the P2 M Ground Theory Heights  Heights Slice Form Lelong Compact ne zero of mem zero Set ba717a31d526 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L22-L26

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

theorem P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_ne_zero_of_mem_zeroSet_ba717a31d526 {I : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    (hℓ : linForm ℓ - 1 ∈ I) {x : Fin n → ℂ} (hx : x ∈ zeroSet I) : x ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceFormLelongCompact».«ne_zero_of_mem_zeroSet» := P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_ne_zero_of_mem_zeroSet_ba717a31d526
