-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_sb_smul
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.sb_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:10.768347+00:00
-- url     : https://prove2.me/theorems/4c5367fc-fcea-434b-8c7e-88b80f95a8d1
-- title:
--   Place Perm Operator Bicommutant Span: sb smul
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the sb smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L73-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/IsOpenCoset.lean#L73-L73

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
omit [AddCommGroup V]

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.sb_smul (c : ℂ) {g : V → ℂ} (hg : SB g) : SB (c • g) := by sorry
