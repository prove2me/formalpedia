-- Prove2me | Theorems.Thm_OverlapRouting_proposition_1
-- name    : OverlapRouting.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:57.710257+00:00
-- url     : https://prove2.me/theorems/eef9e42f-66c3-4885-8077-20c3587d74a6
-- title:
--   Proposition 1 — upper bound on $Z^{AO(\alpha)}$ in terms of $r_{avg}$ (corrected: also holds with a constant $\Gamma_0$ when the printed Corollary 1 has none)
-- statement:
--   Let $N'\ge1$, $Q\ge1$ and $D$ any demand law. There is a constant $\Gamma_0\ge0$, depending only on $N'$, $Q$ and $D$, such that the bound below holds with $\Gamma_3=\Gamma_0$, and also with every constant $\Gamma_3$ of the printed Corollary 1 (every $\Gamma_3$ with $\sum_{j=1}^{M}|\mathbb E[R_j]-r_{avg}|\le\Gamma_3$ for all $M\ge1$), for every depot $x_0$, every $M\ge1$, every set of customer locations $x_1,\dots,x_N$ ($N=N'M$), every $c_{\max}$ with $c_i\le c_{\max}$ for all $i$, every $\alpha$ and every α-optimal labelling,
--   $$Z^{AO(\alpha)}\ \le\ \frac{2Mr_{avg}}{N}\sum_{i=1}^{N}c_i+2\Gamma_3c_{\max}+\alpha\big(2r_{avg}+2\Gamma_3+3\big)L^* .$$
--
--   The leading term is linear in $N$, while the others are of order $c_{\max}+L^*$; this is the upper half of Theorem 1.
--
--   Differences from the source:
--   - correction: "where Γ₃ is the same constant as in Corollary 1" → every constant Γ₃ of the printed Corollary 1, and also one constant Γ₀ ≥ 0 depending only on N′, Q and the demand law (independent of M, N, the depot, the locations, the labelling and α); reason: under the reading below the printed Corollary 1 is false for some laws (N′ = 1, Q = 3, D ≡ 2 gives E[Rⱼ] = 1,1,0,1,1,0,… and Σⱼ|E[Rⱼ] − r_avg| ≥ ⌊M/3⌋(2/3 − 2/M) → ∞), so for those its constant does not exist; the bound itself holds with the constant of the corrected Corollary 1 (Abel summation)
--   - generalization: c_max = sup_{x∈𝒜} ‖x₀ − x‖₂ (p.5) → any real cmax with ‖x₀ − xᵢ‖ ≤ cmax for every customer i; reason: for customers in 𝒜 the paper's c_max is such a bound; specializes
--   - generalization: one α-optimal labelling fixed for the section (p.13) → every real α and every α-optimal labelling; reason: the bound holds for each such labelling; specializes to the paper's fixed one
--   - reading: "D can only take non-negative integer values and has finite support {0} ∪ [u]" (p.5) → any probability mass function p on {0,…,u} (values may have mass 0); reason: the authors' own usage in Appendix A, p.34 (WLOG aperiodic, P[D̄ > Q] > 0); the more general reading, which contains the literal one
--   - encoding: customers labelled 1,…,N along the tour, vehicles j = 1,…,M → 0-based labels 0,…,N′M−1 given by a permutation ℓ (label k is customer ℓ k); 1-based vehicle indices; reason: Lean convention; same instances
--   - encoding: Z^{AO(α)}, the expected travel cost of AO under Algorithm 1 → expectation over the demand vector of the length of the routes Algorithm 1 drives (refill exactly at a stock-out, zero-demand customers skipped); reason: the route of p.10 (rules 1–3) and Algorithm 1, line 13
--   - encoding: E[Rⱼ], the expected number of trips of vehicle j → expTrips: the expectation of rⱼ = ⌈wⱼ/Q⌉ from the recursion (3), over i.i.d. demands; reason: (3) is the paper's own definition of the trip count; Eq. (3) milestone ties it to the driven routes
-- source:
--   Ledvina, Qin, Simchi-Levi & Wei, A New Approach for Vehicle Routing with Stochastic Demand: Combining Route Assignment with Process Flexibility, SSRN 3656374 (PDF of 2022-03-11), https://ssrn.com/abstract=3656374, Proposition 1, p.15 (proof pp.15–16)

import Mathlib
import Definitions.Def_OverlapRouting_vrpOpt
import Definitions.Def_OverlapRouting_DemandLaw
import Definitions.Def_OverlapRouting_costAO
import Definitions.Def_OverlapRouting_ZAO

namespace OverlapRouting

/-- **Proposition 1**, p.15 (Ledvina, Qin, Simchi-Levi & Wei, SSRN 3656374 (2022)): "The quantity
`Z^{AO(α)}` is bounded above by
`Z^{AO(α)} ≤ (2Mr_avg/N) ∑_{i=1}^{N} cᵢ + 2Γ₃c_max + α(2r_avg + 2Γ₃ + 3)L*`, where `Γ₃` is the same
constant as in Corollary 1."

There is a constant `Γ₀ ≥ 0`, depending only on `N′`, `Q` and the demand law, such that the bound
holds with `Γ₃ = Γ₀`, and also with every constant `Γ₃` of the printed Corollary 1 (every `Γ₃` with
`∑_{j=1}^{M} |E[Rⱼ] − r_avg| ≤ Γ₃` for all `M ≥ 1`), for every depot, every `M ≥ 1`, every
configuration of the `N = N′M` customers, every bound `cmax` on their distances to the depot, every
`α` and every `α`-optimal labelling.

**Formalization Note.** The printed Corollary 1 has no constant for some laws with `ℙ[D = 0] = 0`
(`N′ = 1`, `Q = 3`, `D ≡ 2`); the bound still holds for those with the constant `Γ₀`.
`c_max = sup_{x∈𝒜}‖x₀ − x‖` is replaced by any bound `cmax ≥ cᵢ`. -/
theorem proposition_1 (N' Q : ℕ) (hN' : 1 ≤ N') (hQ : 1 ≤ Q) (D : DemandLaw) :
    ∃ Γ₀ : ℝ, 0 ≤ Γ₀ ∧ ∀ Γ₃ : ℝ,
      (Γ₃ = Γ₀ ∨ ∀ M : ℕ, 1 ≤ M →
        ∑ j ∈ Finset.Icc 1 M, |expTrips N' Q D M j - rAvg N' Q D M| ≤ Γ₃) →
      ∀ (x₀ : Point) (M : ℕ), 1 ≤ M → ∀ (x : Fin (N' * M) → Point) (cmax : ℝ),
      (∀ i, dist x₀ (x i) ≤ cmax) → ∀ (α : ℝ) (ℓ : Equiv.Perm (Fin (N' * M))),
      IsAlphaOptimal α x ℓ →
      ZAO N' Q D x₀ M x ℓ ≤
        2 * M * rAvg N' Q D M / ((N' * M : ℕ) : ℝ) * ∑ i, dist x₀ (x i) + 2 * Γ₃ * cmax
          + α * (2 * rAvg N' Q D M + 2 * Γ₃ + 3) * tspOpt x := by sorry

end OverlapRouting
