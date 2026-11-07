-- Prove2me | Theorems.Thm_SpectrumLB_proposition_5_2
-- name    : SpectrumLB.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:36:38.481791+00:00
-- url     : https://prove2.me/theorems/308e075e-7ce1-440b-b695-f260b959a03c
-- title:
--   Proposition 5.2 — sequences in $\mathbb Z_+^{2^{k-1}}$ with equal power sums below $k$ and different at $k$
-- statement:
--   For every integer $k\ge1$ and $K=2^{k-1}$ there are sequences $a,b$ of $K$ positive integers with
--
--   $$
--   \sum_{i=1}^K a_i^{\,j}=\sum_{i=1}^K b_i^{\,j}\quad\text{for all } j<k,\qquad \sum_{i=1}^K a_i^{\,k}\ne\sum_{i=1}^K b_i^{\,k}.
--   $$
--
--   This is a solution of the Prouhet–Tarry–Escott problem (obtainable from the Thue–Morse partition of $\{0,\dots,2^k-1\}$, shifted by one). Such sequences give two product-of-projection ensembles whose moment generating functions agree to order $k$.
--
--   Differences from the source:
--   - reading: k ∈ ℕ → k ≥ 1; reason: K = 2^{k−1} is an integer only for k ≥ 1, and at k = 0 the claim fails (Σ a_i^0 = Σ b_i^0)
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Proposition 5.2, p. 20

import Mathlib

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB

/-- **Proposition 5.2 (Prouhet–Tarry–Escott sequences).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680, Proposition 5.2, p. 20: "For k ∈ N and K = 2^{k−1}, there exist sequences a, b ∈ Z^K_+ with
Σ_{i=1}^K a_i^j = Σ_{i=1}^K b_i^j for all j < k and Σ_{i=1}^K a_i^k ≠ Σ_{i=1}^K b_i^k."

**Formalization Note.** `k ≥ 1` (`K = 2^{k−1}` is not an integer at `k = 0`, and there the claim fails).
`Z_+` is the positive integers. `j` ranges over all `j < k`, including the trivial `j = 0`. -/
theorem proposition_5_2 (k : ℕ) (hk : 1 ≤ k) :
    ∃ a b : Fin (2 ^ (k - 1)) → ℕ, (∀ i, 0 < a i) ∧ (∀ i, 0 < b i) ∧
      (∀ j : ℕ, j < k → ∑ i, a i ^ j = ∑ i, b i ^ j) ∧ ∑ i, a i ^ k ≠ ∑ i, b i ^ k := by sorry

end SpectrumLB
