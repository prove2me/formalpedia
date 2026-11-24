-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_sb_opU
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.sb_opU
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:40.57628+00:00
-- url     : https://prove2.me/theorems/15995a35-e684-4993-8250-89542d85272a
-- title:
--   Place Perm Operator Bicommutant Span: sb op U
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the sb op U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/SqPosOfNe.lean#L36-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/SqPosOfNe.lean#L36-L52

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.sb_opU (b : R) {φ : (ι → R) → ℂ} (hφ : SB φ) : SB (opU ψ h B b φ) := by sorry
