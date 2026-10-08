-- Prove2me | Theorems.Thm_QueueingFundamentals_AdvMarkov_cobham_priority_waits
-- name    : QueueingFundamentals.AdvMarkov.cobham_priority_waits
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T08:23:00.832229+00:00
-- url     : https://prove2.me/theorems/cad649b3-f01e-4695-bde5-5dad4d8dc475
-- title:
--   Eqs. (3.40)–(3.43): Cobham's formula for nonpreemptive priority waiting times
-- statement:
--   Consider $r$ priority classes, class $k$ arriving at rate $\lambda_k > 0$ and served at rate $\mu_k > 0$, and set
--   $$\rho_k = \frac{\lambda_k}{\mu_k}, \qquad \sigma_k = \sum_{i=1}^{k}\rho_i \quad (\sigma_0 = 0), \qquad (3.39)$$
--   with $\sigma_r < 1$. For any real number $\mathrm E[S_0]$ and any numbers $W_q^{(1)},\dots,W_q^{(r)}$, the linear system
--   $$W_q^{(i)} = \frac{\sum_{k=1}^{i}\rho_k W_q^{(k)} + \mathrm E[S_0]}{1-\sigma_{i-1}} \qquad (1 \le i \le r) \qquad (3.40)$$
--   holds if and only if
--   $$W_q^{(i)} = \frac{\mathrm E[S_0]}{(1-\sigma_{i-1})(1-\sigma_i)} \qquad (1 \le i \le r). \qquad (3.41)$$
--   In particular, with $\mathrm E[S_0] = \sum_{k=1}^{r}\rho_k/\mu_k$ (3.42), the system (3.40) holds if and only if
--   $$W_q^{(i)} = \frac{\sum_{k=1}^{r}\rho_k/\mu_k}{(1-\sigma_{i-1})(1-\sigma_i)} \qquad (1 \le i \le r). \qquad (3.43)$$
--
--   So (3.40) has exactly one solution, Cobham's formula, which gives the mean wait in queue of each class in the nonpreemptive $M/M/1$ priority queue.
--
--   **Formalization Note** The book derives the system (3.40) and the value (3.42) of $\mathrm E[S_0]$ by a mean-value argument (the Poisson arrivals see time averages property and Little's formula) that it does not make rigorous; that derivation is not part of this item. The item is the algebraic content: (3.40) has the unique solution (3.41), and (3.43) under (3.42).
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.151–152, Eqs. (3.39), (3.40), (3.41), (3.42), (3.43)

import Mathlib

namespace QueueingFundamentals.AdvMarkov

/-- Eqs. (3.39)–(3.43), pp.151–152 (Cobham's formula), the algebraic part: with `r` nonpreemptive
priority classes, arrival rates `λ_k > 0`, service rates `μ_k > 0`, `ρ_k = λ_k/μ_k`,
`σ_k = ∑_{i=1}^{k} ρ_i` (`σ_0 = 0`) and `σ_r < 1`, the linear system (3.40)
`W^{(i)} = (∑_{k=1}^{i} ρ_k W^{(k)} + E[S_0])/(1 − σ_{i−1})`, `1 ≤ i ≤ r`, holds if and only if
`W^{(i)} = E[S_0]/((1 − σ_{i−1})(1 − σ_i))` for every `1 ≤ i ≤ r` (3.41); in particular, with
`E[S_0] = ∑_{k=1}^{r} ρ_k/μ_k` (3.42), it holds if and only if (3.43). -/
theorem cobham_priority_waits (r : ℕ) (lamk muk : ℕ → ℝ)
    (hlam : ∀ k ∈ Finset.Icc 1 r, 0 < lamk k) (hmu : ∀ k ∈ Finset.Icc 1 r, 0 < muk k)
    (ρ σ : ℕ → ℝ) (hρ : ∀ k, ρ k = lamk k / muk k) (hσ : ∀ k, σ k = ∑ i ∈ Finset.Icc 1 k, ρ i)
    (hσr : σ r < 1) :
    (∀ (ES0 : ℝ) (W : ℕ → ℝ),
      (∀ i ∈ Finset.Icc 1 r, W i = (∑ k ∈ Finset.Icc 1 i, ρ k * W k + ES0) / (1 - σ (i - 1))) ↔
        (∀ i ∈ Finset.Icc 1 r, W i = ES0 / ((1 - σ (i - 1)) * (1 - σ i)))) ∧
    (∀ W : ℕ → ℝ,
      (∀ i ∈ Finset.Icc 1 r, W i =
          (∑ k ∈ Finset.Icc 1 i, ρ k * W k + ∑ k ∈ Finset.Icc 1 r, ρ k / muk k) / (1 - σ (i - 1))) ↔
        (∀ i ∈ Finset.Icc 1 r,
          W i = (∑ k ∈ Finset.Icc 1 r, ρ k / muk k) / ((1 - σ (i - 1)) * (1 - σ i)))) := by sorry

end QueueingFundamentals.AdvMarkov
