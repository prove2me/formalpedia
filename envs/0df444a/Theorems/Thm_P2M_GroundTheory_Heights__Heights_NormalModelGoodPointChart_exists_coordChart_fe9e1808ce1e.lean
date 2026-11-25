-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_exists_coordChart_fe9e1808ce1e
-- name    : P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_exists_coordChart_fe9e1808ce1e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:50.688818+00:00
-- url     : https://prove2.me/theorems/510c7f64-1205-5ea6-a7c8-089241f70854
-- title:
--   P2 M Ground Theory Heights  Heights Normal Model Good Point Chart exists coord Chart fe9e1808ce1e: P2 M Ground Theory Heights  Heights Normal Model Good Point Chart exists coord Chart fe9e1808ce1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Model Good Point Chart exists coord Chart fe9e1808ce1e construction uses the P2 M Ground Theory Heights  Heights Normal Model Good Point Chart exists coord Chart fe9e1808ce1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointChartLemmas.lean#L71-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GoodPointChartLemmas.lean#L71-L177

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointChartLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NormalModelGoodPointChart
open MvPolynomial Topology
open scoped ContDiff
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_exists_coordChart_fe9e1808ce1e {σ κ ι : Type} [Fintype σ] [Fintype κ] [Fintype ι]
    (q : κ ⊕ ι → (σ → ℂ) → ℂ) (a : σ → ℂ) (W : Set (σ → ℂ))
    (hq : ∀ k, AnalyticAt ℂ (q k) a)
    (hinj : ∀ v : σ → ℂ, (∀ k, fderiv ℂ (q k) a v = 0) → v = 0)
    (hcard : Fintype.card κ + Fintype.card ι = Fintype.card σ) (hW : W ∈ 𝓝 a) :
    ∃ (V : Set (σ → ℂ)) (O : Set (κ → ℂ)) (φ : (κ → ℂ) → σ → ℂ),
      IsOpen V ∧ a ∈ V ∧ V ⊆ W ∧ IsOpen O ∧ AnalyticOnNhd ℂ φ O ∧
      (∀ y ∈ O, φ y ∈ V) ∧ (∀ y ∈ O, ∀ i, q (Sum.inl i) (φ y) = y i) ∧
      (∀ y ∈ O, ∀ j, q (Sum.inr j) (φ y) = 0) ∧
      (∀ z ∈ V, (∀ j, q (Sum.inr j) z = 0) →
        (fun i => q (Sum.inl i) z) ∈ O ∧ φ (fun i => q (Sum.inl i) z) = z) ∧
      (∀ y ∈ O, ∀ v, (∀ i, fderiv ℂ (q (Sum.inl i)) (φ y) (fderiv ℂ φ y v) = v i) ∧
        ∀ j, fderiv ℂ (q (Sum.inr j)) (φ y) (fderiv ℂ φ y v) = 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalModelGoodPointChart».«exists_coordChart» := P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_exists_coordChart_fe9e1808ce1e
