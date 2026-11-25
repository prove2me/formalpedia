-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassDivision_in_coordinate_41c122d1492a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassDivision_in_coordinate_41c122d1492a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:26.555082+00:00
-- url     : https://prove2.me/theorems/5e37fb9e-8a94-44dd-8467-9fa462ccc6db
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass Division in coordinate 41c122d1492a: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Comp
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass Division in coordinate 41c122d1492a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass Division in coordinate 41c122d1492a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CoeffEqZeroOfForallEvalEqZero.lean#L61-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CoeffEqZeroOfForallEvalEqZero.lean#L61-L160

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassPolynomialDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CoeffEqZeroOfForallEvalEqZero
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
open Topology Filter
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassDivision_in_coordinate_41c122d1492a (h : WeierstrassPolynomialDivision.Statement)
    {σ : Type} [Fintype σ] [DecidableEq σ] (k : σ) (d : ℕ) (y₀ : Fin d → ℂ) (u₀ : σ → ℂ) (N : ℕ)
    (b : Fin N → (Fin d → ℂ) → ℂ) (f : (Fin d → ℂ) × (σ → ℂ) → ℂ)
    (hb : ∀ j, AnalyticAt ℂ (b j) y₀)
    (hG : ∀ T : ℂ, T ^ N + ∑ j, b j y₀ * T ^ (j : ℕ) = (T - u₀ k) ^ N)
    (hf : AnalyticAt ℂ f (y₀, u₀)) :
    ∃ (q : (Fin d → ℂ) × (σ → ℂ) → ℂ) (e : Fin N → (Fin d → ℂ) × ({m // m ≠ k} → ℂ) → ℂ),
      AnalyticAt ℂ q (y₀, u₀) ∧ (∀ i, AnalyticAt ℂ (e i) (y₀, fun m => u₀ m)) ∧
      ∀ᶠ x in 𝓝 (y₀, u₀), f x = q x * (x.2 k ^ N + ∑ j, b j x.1 * x.2 k ^ (j : ℕ)) +
        ∑ i, e i (x.1, fun m => x.2 m) * x.2 k ^ (i : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«weierstrassDivision_in_coordinate» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassDivision_in_coordinate_41c122d1492a
