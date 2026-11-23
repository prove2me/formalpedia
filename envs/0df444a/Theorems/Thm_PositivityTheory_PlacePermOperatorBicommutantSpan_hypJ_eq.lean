-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_hypJ_eq
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.hypJ_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:51.429965+00:00
-- url     : https://prove2.me/theorems/1d362cda-48c3-45b4-952a-034d53039bba
-- title:
--   Place Perm Operator Bicommutant Span: hyp J eq
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the hyp J eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L72-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L72-L72

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.hypJ_eq (J : Matrix (Fin M) (Fin M) K) : hypJ J = blk 0 1 0 1 0 0 0 0 J := by sorry
