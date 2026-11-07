-- Prove2me | Theorems.Thm_SpectrumLB_lemma_7_1
-- name    : SpectrumLB.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:49.560339+00:00
-- url     : https://prove2.me/theorems/e7c5b5cb-cfae-4c61-8f89-e9b1e19ae1fa
-- title:
--   Lemma 7.1 — $\Psi_j(a)-\Psi_j(b)=O(d^{-1})$ for $j\le k$ and $\Psi_{k+1}(a)-\Psi_{k+1}(b)=\kappa_k+O(d^{-1})$, $\kappa_k\ne0$
-- statement:
--   Let $k\ge1$ and let $a,b$ be sequences of $K$ positive integers with $\sum_ia_i^j=\sum_ib_i^j$ for $1\le j<k$ and $\sum_ia_i^k\ne\sum_ib_i^k$. With $\Psi_j(e)=\mathbf E[\mathrm{tr}X_e^j]/\mathbf E[\mathrm{tr}X_e]^j$ for $X_e\sim\mathrm{PRP}_d(e)$:
--
--   1. there is $C$ such that for every $d\ge1$ divisible by each $a_i,b_i$ and every $1\le j\le k$,
--   $$
--   |\Psi_j(a)-\Psi_j(b)|\le\frac Cd ;
--   $$
--   2. there are a constant $\kappa_k\ne0$ and $C'$ such that for all such $d$,
--   $$
--   \big|\Psi_{k+1}(a)-\Psi_{k+1}(b)-\kappa_k\big|\le\frac{C'}d .
--   $$
--
--   The expected normalized moments of the two ensembles agree to order $k$ and separate at order $k+1$ by a constant independent of $d$.
--
--   Differences from the source:
--   - generalization: a, b from Proposition 5.2 → any K and positive a, b with equal power sums for 1 ≤ j < k and different at k; reason: the proof uses only these properties (paper.md R5); Proposition 5.2's sequences satisfy them
--   - encoding: O(d^{−1}) → |·| ≤ C/d for every d ≥ 1 divisible by each a_i, b_i; reason: the constant absorbs finitely many small d
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Lemma 7.1, Eqs. (7.2)–(7.3), p. 34

import Mathlib
import Definitions.Def_SpectrumLB_psi

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Lemma 7.1 (deterministic moment separation).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Lemma 7.1, Eqs. (7.2)–(7.3), p. 34: "For 1 ≤ j ≤ k, Ψ_j(a) − Ψ_j(b) = O(d^{−1}). There is also a
constant κ_k ≠ 0 such that Ψ_{k+1}(a) − Ψ_{k+1}(b) = κ_k + O(d^{−1})."

**Formalization Note.** `a, b` are positive sequences whose power sums agree for `1 ≤ j < k` and differ at
`k` (reading R5); `k ≥ 1`. `O(d^{−1})` is `≤ C/d` for every `d ≥ 1` divisible by every `a_i`, `b_i`. The
proof's "for j ≤ k − 1" is a slip (paper.md S1); the claim is for `1 ≤ j ≤ k`. -/
theorem lemma_7_1 (k : ℕ) (hk : 1 ≤ k) {K : ℕ} (a b : Fin K → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hpow : ∀ j : ℕ, 1 ≤ j → j < k → ∑ i, a i ^ j = ∑ i, b i ^ j)
    (hsep : ∑ i, a i ^ k ≠ ∑ i, b i ^ k) :
    (∃ C : ℝ, ∀ d : ℕ, 0 < d → (∀ i, a i ∣ d) → (∀ i, b i ∣ d) → ∀ j : ℕ, 1 ≤ j → j ≤ k →
      |psi d a j - psi d b j| ≤ C / d) ∧
    (∃ κ : ℝ, κ ≠ 0 ∧ ∃ C : ℝ, ∀ d : ℕ, 0 < d → (∀ i, a i ∣ d) → (∀ i, b i ∣ d) →
      |psi d a (k + 1) - psi d b (k + 1) - κ| ≤ C / d) := by sorry

end SpectrumLB
