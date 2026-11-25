-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_chartAbsDens_indicator_eq_f674260ff31b
-- name    : P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_chartAbsDens_indicator_eq_f674260ff31b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:54.405909+00:00
-- url     : https://prove2.me/theorems/6891fbde-165d-5538-bd9e-230f00905cfe
-- title:
--   P2 M Ground Theory Heights  Heights Slice Form Lelong Compact chart Abs Dens indicator eq f674260ff31b: P2 M Ground Theory Heights  Heights Slice Form Lelong Compact chart Abs Dens indicator eq f67426
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Form Lelong Compact chart Abs Dens indicator eq f674260ff31b construction uses the P2 M Ground Theory Heights  Heights Slice Form Lelong Compact chart Abs Dens indicator eq f674260ff31b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L65-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L65-L78

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

theorem P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_chartAbsDens_indicator_eq_f674260ff31b {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (w : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {B : Set (Fin n → ℂ)} (i : Fin d)
    (hB : tsupport (ψ i) ⊆ B) : chartAbsDens J A (B.indicator w) ψ = chartAbsDens J A w ψ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceFormLelongCompact».«chartAbsDens_indicator_eq» := P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_chartAbsDens_indicator_eq_f674260ff31b
