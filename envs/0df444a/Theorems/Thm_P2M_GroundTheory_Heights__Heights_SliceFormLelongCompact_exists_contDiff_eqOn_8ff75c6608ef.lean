-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_exists_contDiff_eqOn_8ff75c6608ef
-- name    : P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_exists_contDiff_eqOn_8ff75c6608ef
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:56.117505+00:00
-- url     : https://prove2.me/theorems/c30ca2e9-d579-41ec-b832-8ba71a52ede4
-- title:
--   P2 M Ground Theory Heights  Heights Slice Form Lelong Compact exists cont Diff eq On 8ff75c6608ef: P2 M Ground Theory Heights  Heights Slice Form Lelong Compact exists cont Diff eq On 8ff75c6608ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Form Lelong Compact exists cont Diff eq On 8ff75c6608ef construction uses the P2 M Ground Theory Heights  Heights Slice Form Lelong Compact exists cont Diff eq On 8ff75c6608ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L38-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L38-L63

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

theorem P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_exists_contDiff_eqOn_8ff75c6608ef {Z : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℝ} (hZ : IsClosed Z)
    (hf : SmoothNear Z f) (hfc : HasCompactSupport f) :
    ∃ g : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x ∈ Z, g x = f x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceFormLelongCompact».«exists_contDiff_eqOn» := P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_exists_contDiff_eqOn_8ff75c6608ef
