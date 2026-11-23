-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_impl_D
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.impl_D
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:20.897277+00:00
-- url     : https://prove2.me/theorems/57bf3594-6e53-4786-a852-bfcb7ea7a661
-- title:
--   Place Perm Operator Bicommutant Span: impl D
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the impl D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/SqPosOfNe.lean#L90-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/SqPosOfNe.lean#L90-L116

import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_SqPosOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Matrix
open scoped ENNReal ComplexConjugate MatrixGroups
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι]
variable [TopologicalSpace R] [MeasurableSpace R] {ψ : AddChar R ℂ} {h : R} {B : Matrix ι ι R} {μ : Measure (ι → R)}
variable (H : NAQuad ψ h B μ)
include H

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.impl_D (a : Rˣ) {m : ℝ} (hm : 0 < m)
    (hμ : ∀ s : Set (ι → R), MeasurableSet s → μ ((fun u => (a : R) • u) '' s) = ENNReal.ofReal (m ^ 2) * μ s) :
    Impl ψ h B μ (mMat a) (opD m (a : R)) := by sorry
