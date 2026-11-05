-- Prove2me | Theorems.Thm_OverlapRouting_lemma_2
-- name    : OverlapRouting.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:59.774894+00:00
-- url     : https://prove2.me/theorems/84dc6a2e-c19c-4187-bb1b-5197bcfea05b
-- title:
--   Lemma 2 — $Z^*\le\frac{2\mu}{Q}\sum_i c_i+(1-\frac1Q)(L^*+2c_{\max})$
-- statement:
--   Let $Q\ge1$, $D$ the demand law with mean $\mu$, $x_0$ the depot and $x_1,\dots,x_N$ ($N\ge1$) any customer locations with $c_i=\|x_0-x_i\|_2$. Let $L^*$ be the length of the optimal TSP tour through the customers, and let $c_{\max}$ be any number with $c_i\le c_{\max}$ for all $i$. Then
--   $$Z^*\ \le\ \frac{2\mu}{Q}\sum_{i=1}^{N}c_i+\Big(1-\frac1Q\Big)\big(L^*+2c_{\max}\big).$$
--
--   Together with Lemma 1 it pins $Z^*$ to $\frac{2\mu}{Q}\sum_ic_i$ up to an error of order $L^*+c_{\max}$.
--
--   Differences from the source:
--   - generalization: N = N′M customers in the compact region 𝒜 → any number N ≥ 1 of customers anywhere in ℝ²; reason: Z* does not involve M; specializes
--   - generalization: c_max = sup_{x∈𝒜} ‖x₀ − x‖₂ (p.5) → any real cmax with ‖x₀ − xᵢ‖ ≤ cmax for every customer i; reason: for customers in 𝒜 the paper's c_max is such a bound; specializes
--   - reading: "D can only take non-negative integer values and has finite support {0} ∪ [u]" (p.5) → any probability mass function p on {0,…,u} (values may have mass 0); reason: the authors' own usage in Appendix A, p.34 (WLOG aperiodic, P[D̄ > Q] > 0); the more general reading, which contains the literal one
--   - encoding: "Z* … travel cost of reoptimization" (pp.11–12) → expectation over the demand vector of the infimum of the total length of split-delivery solutions with real delivered amounts; reason: the literal "splittable" model of p.6; for integer demands the bounds of Lemmas 1–2 bracket the integer-amount optimum as well
-- source:
--   Ledvina, Qin, Simchi-Levi & Wei, A New Approach for Vehicle Routing with Stochastic Demand: Combining Route Assignment with Process Flexibility, SSRN 3656374 (PDF of 2022-03-11), https://ssrn.com/abstract=3656374, Lemma 2, p.12

import Mathlib
import Definitions.Def_OverlapRouting_vrpOpt
import Definitions.Def_OverlapRouting_DemandLaw
import Definitions.Def_OverlapRouting_costAO
import Definitions.Def_OverlapRouting_ZAO

namespace OverlapRouting

/-- **Lemma 2**, p.12 (Ledvina, Qin, Simchi-Levi & Wei, SSRN 3656374 (2022)):
`Z* ≤ (2µ/Q) ∑_{i=1}^{N} cᵢ + (1 − 1/Q)(L* + 2c_max)`, where `L*` is the optimal TSP tour length
through the customers and `c_max` bounds the customers' distances to the depot.

**Formalization Note.** `c_max = sup_{x ∈ 𝒜} ‖x₀ − x‖₂` (p.5) is replaced by any `cmax` with
`cᵢ ≤ cmax` for all `i`; for customers in `𝒜` the paper's `c_max` is such a bound. -/
theorem lemma_2 (Q : ℕ) (hQ : 1 ≤ Q) (D : DemandLaw) (x₀ : Point) {N : ℕ} (hN : 0 < N)
    (x : Fin N → Point) (cmax : ℝ) (hcmax : ∀ i, dist x₀ (x i) ≤ cmax) :
    Zstar Q D x₀ x ≤
      2 * D.mean / Q * ∑ i, dist x₀ (x i) + (1 - 1 / (Q : ℝ)) * (tspOpt x + 2 * cmax) := by sorry

end OverlapRouting
