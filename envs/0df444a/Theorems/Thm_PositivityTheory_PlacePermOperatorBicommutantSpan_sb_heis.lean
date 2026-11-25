-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_sb_heis
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.sb_heis
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:14.478605+00:00
-- url     : https://prove2.me/theorems/74c9d744-7c5d-4194-973d-3e49caf949da
-- title:
--   Place Perm Operator Bicommutant Span: sb heis
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the sb heis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/SqPosOfNe.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/SqPosOfNe.lean#L26-L34

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.sb_heis (x y : ι → R) {φ : (ι → R) → ℂ} (hφ : SB φ) : SB (Heisenberg₂ ψ h B x y φ) := by sorry
