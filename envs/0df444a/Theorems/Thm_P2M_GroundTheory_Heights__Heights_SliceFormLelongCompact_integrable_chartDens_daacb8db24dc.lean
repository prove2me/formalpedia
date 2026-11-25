-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_integrable_chartDens_daacb8db24dc
-- name    : P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_integrable_chartDens_daacb8db24dc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:37.61088+00:00
-- url     : https://prove2.me/theorems/05b37115-8f32-445a-acf7-8a9c4cb9aef7
-- title:
--   P2 M Ground Theory Heights  Heights Slice Form Lelong Compact integrable chart Dens daacb8db24dc: P2 M Ground Theory Heights  Heights Slice Form Lelong Compact integrable chart Dens daacb8db24dc
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Form Lelong Compact integrable chart Dens daacb8db24dc construction uses the P2 M Ground Theory Heights  Heights Slice Form Lelong Compact integrable chart Dens daacb8db24dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L80-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L80-L90

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

theorem P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_integrable_chartDens_daacb8db24dc {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) {w : (Fin n → ℂ) → ℝ} {ψ : Fin d → (Fin n → ℂ) → ℝ}
    (hm : Measurable (chartDens J A w ψ)) (hi : Integrable (chartAbsDens J A w ψ)) :
    Integrable (chartDens J A w ψ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceFormLelongCompact».«integrable_chartDens» := P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_integrable_chartDens_daacb8db24dc
