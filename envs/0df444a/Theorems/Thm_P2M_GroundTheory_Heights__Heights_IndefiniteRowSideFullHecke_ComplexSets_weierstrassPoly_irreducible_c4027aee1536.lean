-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPoly_irreducible_c4027aee1536
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPoly_irreducible_c4027aee1536
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:41.476039+00:00
-- url     : https://prove2.me/theorems/591c246b-df00-4efa-ac1c-b0406808596b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass Poly irreducible c4027aee1536: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Se
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass Poly irreducible c4027aee1536 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass Poly irreducible c4027aee1536 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/WeierstrassPolynomialRing.lean#L143-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/WeierstrassPolynomialRing.lean#L143-L192

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassRemainderUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolGermsDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassPolynomialRing
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
open Topology Filter Polynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPoly_irreducible_c4027aee1536 {σ : Type} [Fintype σ] {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0) (hc0 : ∀ j, c j 0 = 0)
    (hirr : Irreducible (polyToGerm σ (weierstrassPoly c hc))) : Irreducible (weierstrassPoly c hc) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«weierstrassPoly_irreducible» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPoly_irreducible_c4027aee1536
