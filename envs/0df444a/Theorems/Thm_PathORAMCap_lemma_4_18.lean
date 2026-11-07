-- Prove2me | Theorems.Thm_PathORAMCap_lemma_4_18
-- name    : PathORAMCap.lemma_4_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:47:26.996026+00:00
-- url     : https://prove2.me/theorems/50872ade-71ca-4c6d-8b6d-9d193a85674c
-- title:
--   Lemma 4.18 — Poisson counts with independent $\mathrm{Exp}(1)$ means are i.i.d. geometric
-- statement:
--   Let $(\Lambda_v)_{v\in V}$ be a finite vector of independent $\mathrm{Exp}(1)$ variables and, conditional on $\Lambda$, let $(C_v)_{v\in V}$ be independent with $C_v\mid\Lambda\sim\mathrm{Poisson}(\Lambda_v)$. Then the $C_v$ are jointly independent and
--
--   $$\mathbb P[C_v=k]=2^{-k-1}\qquad(v\in V,\ k\ge0).$$
--
--   This is the step at which the independent geometric loads of Definition 4.2 appear in the comparison.
--
--   **Formalization Note** Both conclusions are stated at once through the joint law of the mixture: for every $k\in\mathbb N^V$, $\mathbb E_\Lambda\bigl[\prod_v\mathrm{Poisson}(\Lambda_v)\{k_v\}\bigr]=\prod_v2^{-k_v-1}$, with $\Lambda$ distributed as the product of $\mathrm{Exp}(1)$ laws.
--
--   Differences from the source:
--
--   - encoding: C conditionally independent Poisson(Λ_v) given Λ; conclusions: joint independence and the marginal laws → for every k : V → ℕ, ∫ ∏_v Poisson(Λ_v){k_v} dP_Λ = ∏_v 2^{−k_v−1}; reason: the mixture's joint mass function is the left side, and it equals the product of geometric masses exactly when both printed conclusions hold
-- source:
--   Chang, Au, The Minimum Bucket Capacity for Reliable Path ORAM, STOC 2027 submission (manuscript sha256 1762f048…), Lemma 4.18, p.29 (PDF p.32)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PathORAMCap

/-- **Lemma 4.18** (Independent Exponential Means Give Geometric Counts; Chang, Au, *The Minimum Bucket Capacity for Reliable Path ORAM*, STOC 2027 submission (manuscript sha256 1762f048…), p.29 (PDF p.32)): "Let
(Λv)v∈V be a finite vector of independent Exp(1) variables. Conditional on the entire vector Λ, let
(Cv)v∈V be independent with Cv | Λ ∼ Poisson(Λv). Then the Cv are jointly independent, and
P[Cv = k] = 2−k−1 for each v and integer k ≥ 0."

**Formalization Note.** The law of `C` is the mixture: `P[C = k] = E_Λ[∏_v Poisson(Λ_v)(k_v)]` with
`Λ` distributed as the product of `expMeasure 1`. Both conclusions together say that this joint
probability mass function is `∏_v 2^{−k_v−1}` for every `k : V → ℕ`. `Λ_v ≥ 0` almost surely, so
`toNNReal` is the identity on the support. -/
theorem lemma_4_18 (V : Type*) [Fintype V] (k : V → ℕ) :
    ∫⁻ lam : V → ℝ, ∏ v, poissonMeasure (lam v).toNNReal {k v}
        ∂(Measure.pi fun _ : V => expMeasure 1) =
      ∏ v, ((2 : ℝ≥0∞) ^ (k v + 1))⁻¹ := by sorry

end PathORAMCap
