-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_pm_one
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.pm_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:11.804902+00:00
-- url     : https://prove2.me/theorems/949c1615-a108-4459-9d07-282e0b25185e
-- title:
--   Place Perm Operator Bicommutant Span: pm one
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the pm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L49-L53

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_ParAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
variable {K : Type} [CommRing K] {M : ℕ}

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.pm_one : pm (1 : K) 0 (0 : Fin M → K) 1 0 1 = 1 := by sorry
