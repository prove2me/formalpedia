-- Prove2me | Theorems.Thm_OverlapRouting_lemma_3
-- name    : OverlapRouting.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:45.199213+00:00
-- url     : https://prove2.me/theorems/7b665874-5905-4712-9368-83aab495f548
-- title:
--   Lemma 3 — $Z^{AO(\alpha)}\le2\sum_j\mathbb E[R_j](\frac MN\sum_{i\in\mathcal N_j}c_i+L_j)+3\alpha L^*$
-- statement:
--   Let $N'\ge1$, $M\ge1$, $N=N'M$, $Q\ge1$, $D$ any demand law, $x_0$ the depot, $x_1,\dots,x_N$ any customer locations, $\alpha\in\mathbb R$ and a labelling of the customers that is α-optimal. Then
--   $$Z^{AO(\alpha)}\ \le\ 2\sum_{j=1}^{M}\mathbb E[R_j]\Big(\frac{M\sum_{i\in\mathcal N_j}c_i}{N}+L_j\Big)+3\alpha L^* ,$$
--   where $c_i$, $\mathcal N_j$ and $L_j$ refer to the labelled customers.
--
--   It bounds the AO cost by radial terms weighted by the expected trip counts plus a tour term.
--
--   Differences from the source:
--   - reading: "D can only take non-negative integer values and has finite support {0} ∪ [u]" (p.5) → any probability mass function p on {0,…,u} (values may have mass 0); reason: the authors' own usage in Appendix A, p.34 (WLOG aperiodic, P[D̄ > Q] > 0); the more general reading, which contains the literal one
--   - generalization: one α-optimal labelling fixed for the section (p.13) → every real α and every α-optimal labelling; reason: the bound holds for each such labelling; specializes to the paper's fixed one
--   - encoding: customers labelled 1,…,N along the tour, vehicles j = 1,…,M → 0-based labels 0,…,N′M−1 given by a permutation ℓ (label k is customer ℓ k); 1-based vehicle indices; reason: Lean convention; same instances
--   - encoding: Z^{AO(α)}, the expected travel cost of AO under Algorithm 1 → expectation over the demand vector of the length of the routes Algorithm 1 drives (refill exactly at a stock-out, zero-demand customers skipped); reason: the route of p.10 (rules 1–3) and Algorithm 1, line 13
--   - encoding: E[Rⱼ], the expected number of trips of vehicle j → expTrips: the expectation of rⱼ = ⌈wⱼ/Q⌉ from the recursion (3), over i.i.d. demands; reason: (3) is the paper's own definition of the trip count; Eq. (3) milestone ties it to the driven routes
-- source:
--   Ledvina, Qin, Simchi-Levi & Wei, A New Approach for Vehicle Routing with Stochastic Demand: Combining Route Assignment with Process Flexibility, SSRN 3656374 (PDF of 2022-03-11), https://ssrn.com/abstract=3656374, Lemma 3, p.13

import Mathlib
import Definitions.Def_OverlapRouting_vrpOpt
import Definitions.Def_OverlapRouting_DemandLaw
import Definitions.Def_OverlapRouting_costAO
import Definitions.Def_OverlapRouting_ZAO

namespace OverlapRouting

/-- **Lemma 3**, p.13 (Ledvina, Qin, Simchi-Levi & Wei, SSRN 3656374 (2022)): "The quantity
`Z^{AO(α)}` is bounded above by
`Z^{AO(α)} ≤ 2 ∑_{j=1}^{M} E[Rⱼ] (M ∑_{i∈𝒩ⱼ} cᵢ / N + Lⱼ) + 3αL*`."

For `N′ ≥ 1` customers per route, `M ≥ 1` vehicles (`N = N′M`), capacity `Q ≥ 1`, every demand
law, depot, configuration of customer locations, every real `α` and every `α`-optimal labelling.
`cᵢ` and `Lⱼ` are those of the labelled customers. -/
theorem lemma_3 (N' Q : ℕ) (hN' : 1 ≤ N') (hQ : 1 ≤ Q) (D : DemandLaw) (x₀ : Point) (M : ℕ)
    (hM : 1 ≤ M) (x : Fin (N' * M) → Point) (α : ℝ) (ℓ : Equiv.Perm (Fin (N' * M)))
    (hℓ : IsAlphaOptimal α x ℓ) :
    ZAO N' Q D x₀ M x ℓ ≤
      2 * ∑ j ∈ Finset.Icc 1 M, expTrips N' Q D M j *
          ((M : ℝ) * groupDepotDist N' x₀ (extendPoints (x ∘ ℓ)) j / ((N' * M : ℕ) : ℝ) +
            primaryPathLength N' (extendPoints (x ∘ ℓ)) j)
        + 3 * α * tspOpt x := by sorry

end OverlapRouting
