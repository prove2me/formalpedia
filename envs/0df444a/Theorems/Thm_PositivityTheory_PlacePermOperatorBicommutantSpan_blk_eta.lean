-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_blk_eta
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.blk_eta
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:46.576244+00:00
-- url     : https://prove2.me/theorems/615e1336-211d-5e9f-a843-e53defdbc16d
-- title:
--   Place Perm Operator Bicommutant Span: blk eta
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the blk eta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L19-L24

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.blk_eta (g : Matrix (Fin (M + 2)) (Fin (M + 2)) K) :
    g = blk (g 0 0) (g 0 1) (fun j => g 0 j.succ.succ) (g 1 0) (g 1 1) (fun j => g 1 j.succ.succ)
      (fun i => g i.succ.succ 0) (fun i => g i.succ.succ 1) (Matrix.of fun i j => g i.succ.succ j.succ.succ) := by sorry
