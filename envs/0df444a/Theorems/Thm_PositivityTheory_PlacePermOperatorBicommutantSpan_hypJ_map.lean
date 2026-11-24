-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_hypJ_map
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.hypJ_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:02.241807+00:00
-- url     : https://prove2.me/theorems/748ee0b3-8399-45a7-9cb9-e28c5c40f80f
-- title:
--   Place Perm Operator Bicommutant Span: hyp J map
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the hyp J map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L74-L77

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.hypJ_map {L : Type} [CommRing L] (φ : K →+* L) (J : Matrix (Fin M) (Fin M) K) :
    (hypJ J).map φ = hypJ (J.map φ) := by sorry
