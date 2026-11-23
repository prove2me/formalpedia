-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_impl_mul
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.impl_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:24.881473+00:00
-- url     : https://prove2.me/theorems/1e6878e9-68b0-4010-afba-46c6cdf1e5a4
-- title:
--   Place Perm Operator Bicommutant Span: impl mul
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the impl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/SqPosOfNe.lean#L59-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/SqPosOfNe.lean#L59-L73

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
omit H

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.impl_mul {g g' : SL(2, R)} {T T' : ((ι → R) → ℂ) → ((ι → R) → ℂ)} (hT : Impl ψ h B μ g T)
    (hT' : Impl ψ h B μ g' T') : Impl ψ h B μ (g * g') (T ∘ T') := by sorry
