-- Prove2me | Theorems.Thm_SpectrumLB_proposition_5_3
-- name    : SpectrumLB.proposition_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:37:22.428719+00:00
-- url     : https://prove2.me/theorems/24edd992-01f2-4d2b-8e2f-a32d7e2f3029
-- title:
--   Proposition 5.3 — $|\log(f_b/f_a)-\beta_kz^k-\beta_{k+1}z^{k+1}|\le c_k z^{k+2}$ near $0$
-- statement:
--   Let $k\ge2$ be even, and let $a,b$ be sequences of $K$ positive integers with $\sum_ia_i^j=\sum_ib_i^j$ for $1\le j<k$ and $\sum_ia_i^k\ne\sum_ib_i^k$. Then there are real numbers $\beta_k\ne0$, $\beta_{k+1}$ and $c_k>0$ such that for every real $z$ with $|z|<\frac12\min_i\{a_i^{-1},b_i^{-1}\}$,
--
--   $$
--   \Big|\log\frac{f_b(z)}{f_a(z)}-\beta_kz^k-\beta_{k+1}z^{k+1}\Big|\ \le\ c_k\,|z|^{k+2}.
--   $$
--
--   The first $k-1$ Taylor coefficients of $\log f_b/f_a$ vanish, so the log-likelihood ratio of the two ensembles is governed by Jucys–Murphy power sums of order at least $k$.
--
--   Differences from the source:
--   - generalization: k, K, a, b as in Proposition 5.2 → any K and positive a, b with equal power sums for 1 ≤ j < k and different power sums at k; reason: these are the properties of Proposition 5.2's sequences the claim uses (paper.md R5); Proposition 5.2's sequences satisfy them
--   - reading: k ∈ ℕ → k even and k ≥ 2; reason: §5 considers only even k (p. 20); for odd k the printed bound c_k z^{k+2} is negative for z < 0 and fails
--   - encoding: c_k z^{k+2} → c_k |z|^{k+2}; reason: equal for even k (paper.md R6)
--   - encoding: z (unspecified domain) → z real; reason: every use evaluates at real numbers or Hermitian operators (paper.md R6)
--   - encoding: |z| < ½ min_i{a_i^{−1}, b_i^{−1}} → |z| < 1/(2a_i) and |z| < 1/(2b_i) for every i; reason: equivalent for K ≥ 1, which the hypotheses force
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Proposition 5.3, Eq. (5.4), p. 20

import Mathlib
import Definitions.Def_SpectrumLB_fA

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Proposition 5.3 (expansion of `log(f_b/f_a)`).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Proposition 5.3, Eq. (5.4), p. 20: "For k, K, a, b as in Proposition 5.2, there are β_k ≠ 0, β_{k+1}
and c_k > 0 such that |log(f_b(z)/f_a(z)) − β_k z^k − β_{k+1} z^{k+1}| ≤ c_k z^{k+2}, whenever
|z| < ½ min_i{a_i^{−1}, b_i^{−1}}."

**Formalization Note.** `k` is even and `≥ 2` (§5, p. 20: "we will only consider even k"), so
`z^{k+2} = |z|^{k+2}` (reading R6); `z` is real. "a, b as in Proposition 5.2" is replaced by its conclusion
(positive entries, equal power sums for `1 ≤ j < k`, different at `k`), for any length `K` (reading R5).
The radius condition is written per index: `|z| < 1/(2a_i)` and `|z| < 1/(2b_i)` for all `i`. -/
theorem proposition_5_3 (k : ℕ) (hk : Even k) (hk2 : 2 ≤ k) {K : ℕ} (a b : Fin K → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hpow : ∀ j : ℕ, 1 ≤ j → j < k → ∑ i, a i ^ j = ∑ i, b i ^ j)
    (hsep : ∑ i, a i ^ k ≠ ∑ i, b i ^ k) :
    ∃ βk βk1 ck : ℝ, βk ≠ 0 ∧ 0 < ck ∧ ∀ z : ℝ,
      (∀ i, |z| < 1 / (2 * (a i : ℝ)) ∧ |z| < 1 / (2 * (b i : ℝ))) →
        |Real.log (fA b z / fA a z) - βk * z ^ k - βk1 * z ^ (k + 1)| ≤ ck * |z| ^ (k + 2) := by sorry

end SpectrumLB
