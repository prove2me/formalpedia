-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrass_remainder_eq_zero_e4d63f335f60
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrass_remainder_eq_zero_e4d63f335f60
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:50.259569+00:00
-- url     : https://prove2.me/theorems/eb653d5c-0400-4e11-9c36-371160fd0220
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass remainder eq zero e4d63f335f60: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex S
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass remainder eq zero e4d63f335f60 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass remainder eq zero e4d63f335f60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/WeierstrassRemainderUnique.lean#L92-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/WeierstrassRemainderUnique.lean#L92-L151

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassRemainderUnique
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrass_remainder_eq_zero_e4d63f335f60 {σ : Type} [Fintype σ] {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, ContinuousAt (c j) 0) (hc0 : ∀ j, c j 0 = 0) (a : Fin d → (σ → ℂ) → ℂ)
    (q : (Option σ → ℂ) → ℂ) (hq : AnalyticAt ℂ q 0)
    (h : ∀ᶠ x in 𝓝 (0 : Option σ → ℂ),
      ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ) = q x * weierstrassPolynomial c x) :
    ∀ j, ∀ᶠ z in 𝓝 (0 : σ → ℂ), a j z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«weierstrass_remainder_eq_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrass_remainder_eq_zero_e4d63f335f60
