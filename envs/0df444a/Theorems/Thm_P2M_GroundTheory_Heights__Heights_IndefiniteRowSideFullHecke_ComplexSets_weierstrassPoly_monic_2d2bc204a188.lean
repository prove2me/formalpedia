-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPoly_monic_2d2bc204a188
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPoly_monic_2d2bc204a188
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:16.955895+00:00
-- url     : https://prove2.me/theorems/d6ba5094-d46e-4317-b61f-b4b5151b31e4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass Poly monic 2d2bc204a188: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets wei
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass Poly monic 2d2bc204a188 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass Poly monic 2d2bc204a188 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/WeierstrassPolynomialRing.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/WeierstrassPolynomialRing.lean#L54-L56

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPoly_monic_2d2bc204a188 {σ : Type} [Fintype σ] {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0) : (weierstrassPoly c hc).Monic := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«weierstrassPoly_monic» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPoly_monic_2d2bc204a188
