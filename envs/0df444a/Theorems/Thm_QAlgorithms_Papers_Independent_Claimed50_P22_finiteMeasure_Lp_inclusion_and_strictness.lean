-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P22_finiteMeasure_Lp_inclusion_and_strictness
-- name    : QAlgorithms.Papers.Independent.Claimed50.P22.finiteMeasure_Lp_inclusion_and_strictness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:13:25.638009+00:00
-- url     : https://prove2.me/theorems/28df5702-9810-4692-a204-bda5bad5bf22
-- title:
--   Continuous and strict inclusions between finite Lp spaces
-- statement:
--   Let $(X,\mu)$ be a finite measure space, and let $1\le p<q<\infty$ be finite real exponents.
--
--   1. The canonical inclusion $L^q(X,\mu;\mathbb C)\hookrightarrow L^p(X,\mu;\mathbb C)$ is a continuous linear injection, sending each equivalence class to the same function almost everywhere.
--   2. If $X$ is the disjoint union of measurable sets $X_n$, indexed by $n\ge1$, with $0<\mu(X_n)\le2^{-n}\mu(X)$, then the inclusion is strict:
--
--   $$\exists f:\quad f\in L^p(X,\mu),\qquad f\notin L^q(X,\mu).$$
--
--   3. Every measurable subset $Y\subseteq[0,1]$ of positive Lebesgue measure admits such a disjoint measurable partition, with $\mu(X)$ replaced by the measure of $Y$.
--
--   These facts distinguish the integrability regimes used in the multiplication representations. The formal statement encodes finite exponents as finite extended nonnegative reals and shifts sequence indices from $n\ge1$ to $n+1$ for $n\in\mathbb N$.
-- source:
--   On Differentiable Vectors for Representations of Infinite Dimensional Lie Groups, arXiv:1002.1602v3, PDF p. 32, Remark 10.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22

namespace QAlgorithms.Papers.Independent.Claimed50.P22

open Set Filter Topology

universe u v w z

/-- Remark 10.1(a–c), PDF p. 32: continuous inclusions between finite
Lp exponents, strictness under a positive dyadic measurable partition, and
existence of such partitions on every positive-measure subset of [0,1].
The a.e. formula fixes the inclusion, rather than merely asserting that
some unrelated continuous injection exists. -/
theorem finiteMeasure_Lp_inclusion_and_strictness
    {X : Type u} [MeasurableSpace X]
    (mu : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure mu]
    (p q : ENNReal) (hp : 1 ≤ p) (hpq : p < q) (hq : q < ⊤) :
    letI : Fact (1 ≤ p) := ⟨hp⟩
    letI : Fact (1 ≤ q) := ⟨le_trans hp (le_of_lt hpq)⟩
    (∃ J : MeasureTheory.Lp ℂ q mu →L[ℂ] MeasureTheory.Lp ℂ p mu,
      Function.Injective J ∧
      ∀ f : MeasureTheory.Lp ℂ q mu, ∀ᵐ x ∂mu, J f x = f x) ∧
    ((∃ A : ℕ → Set X,
      (∀ n, MeasurableSet (A n)) ∧
      (Pairwise (fun n m => Disjoint (A n) (A m))) ∧
      (⋃ n, A n) = Set.univ ∧
      ∀ n, 0 < mu (A n) ∧
        mu (A n) ≤ ((2 : ENNReal) ^ (n + 1))⁻¹ * mu Set.univ) →
      ∃ f : X → ℂ, MeasureTheory.MemLp f p mu ∧ ¬ MeasureTheory.MemLp f q mu) ∧
    (∀ Y : Set ℝ, MeasurableSet Y → Y ⊆ Set.Icc 0 1 →
      0 < MeasureTheory.volume Y →
      ∃ A : ℕ → Set ℝ,
        (∀ n, MeasurableSet (A n)) ∧
        (Pairwise (fun n m => Disjoint (A n) (A m))) ∧
        (⋃ n, A n) = Y ∧
        ∀ n, 0 < MeasureTheory.volume (A n) ∧
          MeasureTheory.volume (A n) ≤
            ((2 : ENNReal) ^ (n + 1))⁻¹ * MeasureTheory.volume Y) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P22
