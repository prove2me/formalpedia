-- Prove2me | Theorems.Thm_OverlapRouting_corollary_1
-- name    : OverlapRouting.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:01.919688+00:00
-- url     : https://prove2.me/theorems/ac4ecd53-e4fc-4eef-967f-3c7f7cbc7251
-- title:
--   Corollary 1 (corrected: the printed bound when $\mathbb P[D=0]>0$; bounded partial sums $|\sum_{k\le j}(\mathbb E[R_k]-r_{avg})|\le\Gamma_3$ for every law)
-- statement:
--   Let $N'\ge1$, $Q\ge1$ and $D$ any demand law.
--
--   1. If $\mathbb P[D=0]>0$ (in particular for the literal support $\{0\}\cup[u]$), there is a constant $\Gamma_3$, independent of $M$ and $N$, such that for every $M\ge1$
--   $$\sum_{j=1}^{M}\big|\mathbb E[R_j]-r_{avg}\big|\ \le\ \Gamma_3 .$$
--   2. For every law $D$ there is a constant $\Gamma_3$, independent of $M$ and $N$, such that for every $M\ge1$ and every $j\le M$
--   $$\Big|\sum_{k=1}^{j}\big(\mathbb E[R_k]-r_{avg}\big)\Big|\ \le\ \Gamma_3 .$$
--
--   Bounded partial sums of the deviations (part 2) are what the summation by parts in Proposition 1 and Lemma 5 uses for periodic excess chains.
--
--   Differences from the source:
--   - correction: Σ_{j=1}^{M} |E[Rⱼ] − r_avg| ≤ Γ₃ → that bound under ℙ[D = 0] > 0, and for every law |Σ_{k=1}^{j} (E[R_k] − r_avg)| ≤ Γ₃ for all j ≤ M; reason: under the reading below the printed bound is false for some laws with ℙ[D = 0] = 0: N′ = 1, Q = 3, D ≡ 2 gives Σⱼ|E[Rⱼ] − r_avg| ≥ ⌊M/3⌋(2/3 − 2/M) → ∞; the partial-sum form follows from the corrected Lemma 4
--   - generalization: the printed bound under the literal support {0} ∪ [u] (every value has positive mass) → the printed bound under ℙ[D = 0] > 0 alone; reason: every state of the excess chain moves to 0 with probability at least ℙ[D = 0]^{N′}, so convergence is geometric; specializes to the literal support
--   - reading: "D can only take non-negative integer values and has finite support {0} ∪ [u]" (p.5) → any probability mass function p on {0,…,u} (values may have mass 0); reason: the authors' own usage in Appendix A, p.34 (WLOG aperiodic, P[D̄ > Q] > 0); the more general reading, which contains the literal one
--   - encoding: E[Rⱼ], the expected number of trips of vehicle j → expTrips: the expectation of rⱼ = ⌈wⱼ/Q⌉ from the recursion (3), over i.i.d. demands; reason: (3) is the paper's own definition of the trip count; Eq. (3) milestone ties it to the driven routes
-- source:
--   Ledvina, Qin, Simchi-Levi & Wei, A New Approach for Vehicle Routing with Stochastic Demand: Combining Route Assignment with Process Flexibility, SSRN 3656374 (PDF of 2022-03-11), https://ssrn.com/abstract=3656374, Corollary 1, p.15

import Mathlib
import Definitions.Def_OverlapRouting_vrpOpt
import Definitions.Def_OverlapRouting_DemandLaw
import Definitions.Def_OverlapRouting_costAO
import Definitions.Def_OverlapRouting_ZAO

namespace OverlapRouting

/-- **Corollary 1**, p.15 (Ledvina, Qin, Simchi-Levi & Wei, SSRN 3656374 (2022)), with a correction
for laws with `ℙ[D = 0] = 0`:
1. (the printed bound) if `ℙ[D = 0] > 0`, which holds for the literal support `{0} ∪ [u]`, there is
   a constant `Γ₃`, independent of `M` and `N`, with `∑_{j=1}^{M} |E[Rⱼ] − r_avg| ≤ Γ₃` for all `M ≥ 1`;
2. for every law `D` there is a constant `Γ₃`, independent of `M` and `N`, such that every partial
   sum of the deviations is bounded: `|∑_{k=1}^{j} (E[R_k] − r_avg)| ≤ Γ₃` for all `M ≥ 1`, `j ≤ M`.

**Formalization Note.** Without `ℙ[D = 0] > 0` the printed sum can grow linearly in `M`: `N′ = 1`,
`Q = 3`, `D ≡ 2`. -/
theorem corollary_1 (N' Q : ℕ) (hN' : 1 ≤ N') (hQ : 1 ≤ Q) (D : DemandLaw) :
    (0 < D.p 0 → ∃ Γ₃ : ℝ, ∀ M : ℕ, 1 ≤ M →
      ∑ j ∈ Finset.Icc 1 M, |expTrips N' Q D M j - rAvg N' Q D M| ≤ Γ₃) ∧
    ∃ Γ₃ : ℝ, ∀ M j : ℕ, 1 ≤ M → j ≤ M →
      |∑ k ∈ Finset.Icc 1 j, (expTrips N' Q D M k - rAvg N' Q D M)| ≤ Γ₃ := by sorry

end OverlapRouting
