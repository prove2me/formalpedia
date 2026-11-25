-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_CO_sup
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.CO.sup
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:26.747263+00:00
-- url     : https://prove2.me/theorems/5e17677b-2cf8-5df6-82ff-63e90aedfb33
-- title:
--   CO: sup
-- statement:
--   The CO construction uses the sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L40-L41

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
variable [IsTopologicalAddGroup V]

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.CO.sup {L L' : AddSubgroup V} (h : CO L) (h' : CO L') : CO (L ⊔ L') := by sorry
