-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_continuous_UJ
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.continuous_UJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:03.296497+00:00
-- url     : https://prove2.me/theorems/596a1a3e-4e2c-41c8-9011-b5fb783f92dc
-- title:
--   Place Perm Operator Bicommutant Span: continuous UJ
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the continuous UJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L184-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L184-L203

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
variable (s : K →+* K) (J : Matrix (Fin M) (Fin M) K)
variable {s J}

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.continuous_UJ {n : ℕ} [TopologicalSpace K] [IsTopologicalRing K] {s : K →+* K} (hs : Continuous s)
    {J Ji : Matrix (Fin n) (Fin n) K} (hJ : Ji * J = 1) :
    Topology.IsInducing fun g : UJ s J => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by sorry
