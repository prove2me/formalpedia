-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_ind_add
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.ind_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:30.910401+00:00
-- url     : https://prove2.me/theorems/9a941099-d5fc-4f1b-88a8-1dbc35c216fd
-- title:
--   Place Perm Operator Bicommutant Span: ind add
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the ind add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L33-L34

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
omit [TopologicalSpace V]

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.ind_add {a l : V} {L : AddSubgroup V} (x : V) (hl : l ∈ L) : ind a L (x + l) = ind a L x := by sorry
