-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_bsym
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.bsym
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:32.828956+00:00
-- url     : https://prove2.me/theorems/7afbd9cc-e1b7-42ee-b974-52ca0db7a339
-- title:
--   Place Perm Operator Bicommutant Span: bsym
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the bsym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/SqPosOfNe.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/SqPosOfNe.lean#L14-L15

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.bsym {B : Matrix ι ι R} (hB : B.IsSymm) (x y : ι → R) : x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := by sorry
