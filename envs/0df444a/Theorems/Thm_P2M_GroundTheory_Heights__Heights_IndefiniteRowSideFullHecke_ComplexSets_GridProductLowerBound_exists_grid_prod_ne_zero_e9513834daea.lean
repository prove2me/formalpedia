-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GridProductLowerBound_exists_grid_prod_ne_zero_e9513834daea
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GridProductLowerBound_exists_grid_prod_ne_zero_e9513834daea
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:54.339505+00:00
-- url     : https://prove2.me/theorems/d736ccc5-3108-4a7d-8a88-6b6b33cb3362
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Grid Product Lower Bound exists grid prod ne zero e9513834daea: P2 M Ground Theory Heights  Heights Indefinite Row Side
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Grid Product Lower Bound exists grid prod ne zero e9513834daea construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Grid Product Lower Bound exists grid prod ne zero e9513834daea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGridProductLowerBound.lean#L9-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGridProductLowerBound.lean#L9-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGridProductLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGridProductLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GridProductLowerBound_exists_grid_prod_ne_zero_e9513834daea {σ : Type} [Fintype σ] {N k : ℕ} (hk : k ≤ N)
    (v : Fin k → σ → ℂ) (hv : ∀ m, v m ≠ 0) :
    ∃ u : σ → Fin (N + 1), ∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«GridProductLowerBound».«exists_grid_prod_ne_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GridProductLowerBound_exists_grid_prod_ne_zero_e9513834daea
