-- Prove2me | Theorems.Thm_OverlapRouting_lemma_4
-- name    : OverlapRouting.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:50.156682+00:00
-- url     : https://prove2.me/theorems/6f21d1d5-cce1-4a24-968f-ce80776799cf
-- title:
--   Lemma 4 (corrected: the printed bound when $\mathbb P[D=0]>0$; bounded cumulative deviation $|\sum_{k\le j}\mathbb E[R_k]-jr^\infty|\le\Gamma$ for every law)
-- statement:
--   Let $N'\ge1$, $Q\ge1$ and $D$ any demand law.
--
--   1. If $\mathbb P[D=0]>0$ (in particular for the literal support $\{0\}\cup[u]$), there are constants $0<\gamma<1$, $\Gamma_1$ and $\Gamma_2$, independent of $M$ and $N$, such that for every $1\le j\le M$
--   $$\big|\mathbb E[R_j]-r_{avg}\big|\ \le\ \Gamma_1\gamma^j+\frac{\Gamma_2}{M}.$$
--   2. For every law $D$ there are constants $r^\infty$ and $\Gamma$, independent of $M$ and $N$, such that for every $M$ and every $j\le M$
--   $$\Big|\sum_{k=1}^{j}\mathbb E[R_k]-j\,r^\infty\Big|\ \le\ \Gamma .$$
--
--   Part 2 gives $r_{avg}\to r^\infty$ at rate $\Gamma/M$; it is the form of Lemma 4 that the proofs of Proposition 1, Lemma 5 and Theorem 1 need when the excess chain is periodic.
--
--   Differences from the source:
--   - correction: |E[Rⱼ] − r_avg| ≤ Γ₁γʲ + Γ₂/M for some 0 < γ < 1 and constants Γ₁, Γ₂ → that bound under ℙ[D = 0] > 0, and for every law ∃ r∞ Γ, |Σ_{k=1}^{j} E[R_k] − j·r∞| ≤ Γ for all j ≤ M; reason: under the reading below the printed bound is false for laws with ℙ[D = 0] = 0 whose excess chain is periodic: N′ = 1, Q = 3, D ≡ 2 gives E[Rⱼ] = 1,1,0,1,1,0,… (verification file), so |E[R₃ₖ] − r_avg| ≥ 2/3 − 2/M while Γ₁γʲ + Γ₂/M → 0; Appendix A's aperiodicity is not without loss of generality
--   - generalization: the printed bound under the literal support {0} ∪ [u] (every value has positive mass) → the printed bound under ℙ[D = 0] > 0 alone; reason: every state of the excess chain moves to 0 with probability at least ℙ[D = 0]^{N′}, so convergence is geometric; specializes to the literal support
--   - reading: "D can only take non-negative integer values and has finite support {0} ∪ [u]" (p.5) → any probability mass function p on {0,…,u} (values may have mass 0); reason: the authors' own usage in Appendix A, p.34 (WLOG aperiodic, P[D̄ > Q] > 0); the more general reading, which contains the literal one
--   - encoding: E[Rⱼ], the expected number of trips of vehicle j → expTrips: the expectation of rⱼ = ⌈wⱼ/Q⌉ from the recursion (3), over i.i.d. demands; reason: (3) is the paper's own definition of the trip count; Eq. (3) milestone ties it to the driven routes
-- source:
--   Ledvina, Qin, Simchi-Levi & Wei, A New Approach for Vehicle Routing with Stochastic Demand: Combining Route Assignment with Process Flexibility, SSRN 3656374 (PDF of 2022-03-11), https://ssrn.com/abstract=3656374, Lemma 4, p.15 (proof Appendix A, pp.35–36)

import Mathlib
import Definitions.Def_OverlapRouting_vrpOpt
import Definitions.Def_OverlapRouting_DemandLaw
import Definitions.Def_OverlapRouting_costAO
import Definitions.Def_OverlapRouting_ZAO

namespace OverlapRouting

/-- **Lemma 4**, p.15 (Ledvina, Qin, Simchi-Levi & Wei, SSRN 3656374 (2022)), with a correction for
laws with `ℙ[D = 0] = 0`:
1. (the printed bound) if `ℙ[D = 0] > 0`, which holds for the literal support `{0} ∪ [u]`, there are
   constants `0 < γ < 1`, `Γ₁`, `Γ₂`, independent of `M` and `N`, with
   `|E[Rⱼ] − r_avg| ≤ Γ₁γʲ + Γ₂/M` for all `1 ≤ j ≤ M`;
2. for every law `D` there are constants `r∞` and `Γ`, independent of `M` and `N`, such that the
   cumulative expected trip counts stay within `Γ` of `j·r∞`:
   `|∑_{k=1}^{j} E[R_k] − j r∞| ≤ Γ` for all `j ≤ M`.

**Formalization Note.** The printed bound fails without `ℙ[D = 0] > 0` when the excess-capacity
chain is periodic: for `N′ = 1`, `Q = 3`, `D ≡ 2`, `E[Rⱼ] = 1, 1, 0, 1, 1, 0, …`. With `ℙ[D = 0] > 0`
every state of the chain moves to `0` with probability at least `ℙ[D = 0]^{N′}`, so the chain
converges geometrically. -/
theorem lemma_4 (N' Q : ℕ) (hN' : 1 ≤ N') (hQ : 1 ≤ Q) (D : DemandLaw) :
    (0 < D.p 0 → ∃ Γ₁ Γ₂ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∀ M j : ℕ, 1 ≤ j → j ≤ M →
      |expTrips N' Q D M j - rAvg N' Q D M| ≤ Γ₁ * γ ^ j + Γ₂ / M) ∧
    ∃ rInf Γ : ℝ, ∀ M j : ℕ, j ≤ M →
      |∑ k ∈ Finset.Icc 1 j, expTrips N' Q D M k - j * rInf| ≤ Γ := by sorry

end OverlapRouting
