-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_weil_id
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.weil_id
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:51:51.31883+00:00
-- url     : https://prove2.me/theorems/5cc3274a-c6ba-5ae3-8582-599933ec421a
-- title:
--   Place Perm Operator Bicommutant Span: weil id
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the weil id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/SqPosOfNe.lean#L189-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/SqPosOfNe.lean#L189-L203

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.weil_id (b : Rˣ) {m : ℝ} (hm : 0 < m) (hμ : ∀ s : Set (ι → R), MeasurableSet s →
      μ ((fun u => ((b⁻¹ : Rˣ) : R) • u) '' s) = ENNReal.ofReal (m ^ 2) * μ s) :
    ∃ γ : ℂ, ‖γ‖ = 1 ∧ ∀ φ, SB φ → opU ψ h B (b : R) (fou (chiB ψ B) μ φ) =
      γ • fou (chiB ψ B) μ (opU ψ h B (-((b⁻¹ : Rˣ) : R)) (opD m ((b⁻¹ : Rˣ) : R)
        (fou (chiB ψ B) μ (opU ψ h B (-((b⁻¹ : Rˣ) : R)) φ)))) := by sorry
