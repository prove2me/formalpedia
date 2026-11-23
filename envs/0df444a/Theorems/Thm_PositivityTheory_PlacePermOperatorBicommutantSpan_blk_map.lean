-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_blk_map
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.blk_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:40.031808+00:00
-- url     : https://prove2.me/theorems/ec6964cc-e4a7-4673-a0c5-f3cd7b88af9c
-- title:
--   Place Perm Operator Bicommutant Span: blk map
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the blk map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L55-L59

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.blk_map {L : Type} [CommRing L] (φ : K → L) (a b c d : K) (r s u w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    (blk a b r c d s u w U).map φ = blk (φ a) (φ b) (φ ∘ r) (φ c) (φ d) (φ ∘ s) (φ ∘ u) (φ ∘ w) (U.map φ) := by sorry
