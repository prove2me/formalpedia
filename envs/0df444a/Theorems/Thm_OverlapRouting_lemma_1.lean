-- Prove2me | Theorems.Thm_OverlapRouting_lemma_1
-- name    : OverlapRouting.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:50.894018+00:00
-- url     : https://prove2.me/theorems/42aa1e81-e328-4ada-81a4-0e373430c9b8
-- title:
--   Lemma 1 — $Z^*\ge\frac{2\mu}{Q}\sum_i c_i$
-- statement:
--   Let $Q\ge1$ be the vehicle capacity, $D$ the demand law with mean $\mu$, $x_0$ the depot and $x_1,\dots,x_N$ any customer locations in the plane, with $c_i=\|x_0-x_i\|_2$. Then the expected reoptimization cost satisfies
--   $$Z^*\ \ge\ \frac{2\mu}{Q}\sum_{i=1}^{N}c_i .$$
--
--   This is the radial lower bound that serves as the denominator in the proof of Theorem 1.
--
--   Differences from the source:
--   - generalization: N = N′M customers in the compact region 𝒜 → any number N of customers anywhere in ℝ²; reason: Z* does not involve M or 𝒜; specializes
--   - reading: "D can only take non-negative integer values and has finite support {0} ∪ [u]" (p.5) → any probability mass function p on {0,…,u} (values may have mass 0); reason: the authors' own usage in Appendix A, p.34 (WLOG aperiodic, P[D̄ > Q] > 0); the more general reading, which contains the literal one
--   - encoding: "Z* … travel cost of reoptimization" (pp.11–12) → expectation over the demand vector of the infimum of the total length of split-delivery solutions with real delivered amounts; reason: the literal "splittable" model of p.6; for integer demands the bounds of Lemmas 1–2 bracket the integer-amount optimum as well
-- source:
--   Ledvina, Qin, Simchi-Levi & Wei, A New Approach for Vehicle Routing with Stochastic Demand: Combining Route Assignment with Process Flexibility, SSRN 3656374 (PDF of 2022-03-11), https://ssrn.com/abstract=3656374, Lemma 1, p.12

import Mathlib
import Definitions.Def_OverlapRouting_vrpOpt
import Definitions.Def_OverlapRouting_DemandLaw
import Definitions.Def_OverlapRouting_costAO
import Definitions.Def_OverlapRouting_ZAO

namespace OverlapRouting

/-- **Lemma 1**, p.12 (Ledvina, Qin, Simchi-Levi & Wei, SSRN 3656374 (2022)):
`Z* ≥ (2µ/Q) ∑_{i=1}^{N} cᵢ`, where `cᵢ = ‖x₀ − xᵢ‖₂` is the distance from customer `i` to the
depot, `µ` the mean demand and `Q` the vehicle capacity.

It holds for every configuration of `N` customer locations, every depot and every demand law. -/
theorem lemma_1 (Q : ℕ) (hQ : 1 ≤ Q) (D : DemandLaw) (x₀ : Point) {N : ℕ} (x : Fin N → Point) :
    2 * D.mean / Q * ∑ i, dist x₀ (x i) ≤ Zstar Q D x₀ x := by sorry

end OverlapRouting
