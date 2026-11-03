-- Prove2me | Theorems.Thm_RandomOrderCRS_proposition_11
-- name    : RandomOrderCRS.proposition_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:23.663309+00:00
-- url     : https://prove2.me/theorems/1b3a339b-c5d0-410c-976c-5ba116d2c516
-- title:
--   Proposition 11 — integral of a product with a single-crossing factor
-- statement:
--   Let $\lambda,\phi:[0,1]\to\mathbb R$ be integrable, with $\lambda\ge0$ and $\lambda$ non-increasing. Suppose that there is $0\le z_c\le1$ such that $\phi(z)\ge0$ for all $z\in[0,z_c]$ and $\phi(z)\le0$ for all $z\in[z_c,1]$. Then
--
--   $$\int_0^1\lambda(z)\phi(z)\,dz\ge\lambda(z_c)\int_0^1\phi(z)\,dz.$$
--
--   This elementary bound is applied in Lemma 4 to a function that changes sign, where a pointwise comparison is impossible.
--
--   Differences from the source:
--   - encoding: $\lambda,\phi:[0,1]\to\mathbb R$ → functions on $\mathbb R$, with all hypotheses on $[0,1]$ and integrability as `IntervalIntegrable`; reason: values outside $[0,1]$ do not enter
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Proposition 11, p.21

import Mathlib

namespace RandomOrderCRS

/-- Proposition 11, MacRury, Ma & Grammel, arXiv:2209.07520v2, p.21: "Suppose that λ, φ : [0, 1] → ℝ
are integrable, λ ≥ 0, and λ is non-increasing. Moreover, assume that there exists 0 ≤ z_c ≤ 1 such
that φ(z) ≥ 0 for all z ∈ [0, z_c], and φ(z) ≤ 0 for all z ∈ [z_c, 1]. Then, ∫₀¹ λ(z) φ(z) dz ≥
λ(z_c) ∫₀¹ φ(z) dz."

**Formalization Note.** Integrability is `IntervalIntegrable`, so the integrals are not the junk
value `0`. The functions are defined on `ℝ`, and only their values on `[0, 1]` matter. -/
theorem proposition_11 (lam φ : ℝ → ℝ) (hlam : IntervalIntegrable lam MeasureTheory.volume 0 1)
    (hφ : IntervalIntegrable φ MeasureTheory.volume 0 1)
    (hlam0 : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ lam z) (hanti : AntitoneOn lam (Set.Icc (0 : ℝ) 1))
    (zc : ℝ) (hzc : zc ∈ Set.Icc (0 : ℝ) 1) (hpos : ∀ z ∈ Set.Icc 0 zc, 0 ≤ φ z)
    (hneg : ∀ z ∈ Set.Icc zc 1, φ z ≤ 0) :
    lam zc * ∫ z in (0 : ℝ)..1, φ z ≤ ∫ z in (0 : ℝ)..1, lam z * φ z := by sorry

end RandomOrderCRS
