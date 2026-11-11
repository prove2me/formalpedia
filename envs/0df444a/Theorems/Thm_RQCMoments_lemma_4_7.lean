-- Prove2me | Theorems.Thm_RQCMoments_lemma_4_7
-- name    : RQCMoments.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:08:19.8683+00:00
-- url     : https://prove2.me/theorems/037aa008-2993-41c5-ad2f-8bb2c633e771
-- title:
--   Lemma 4.7 — polynomial minorant $L_i=U_i-\ell_i^2$ of the indicator of $(-\infty,x_i]$
-- statement:
--   Let $\ell>1$ be an integer and $x_1<\dots<x_\ell$ real numbers, and let $1_{x_i}$ be the indicator function of $(-\infty,x_i]$. Then for every $i\in[\ell]$ there is a real polynomial $L_i$ of degree at most $2\ell-2$ such that
--   1. $L_i(x)\le 1_{x_i}(x)$ for all $x\in\mathbb R$;
--   2. $L_i(x_j)=1$ if $j<i$ and $L_i(x_j)=0$ if $j\ge i$;
--   3. $L_i'(x_j)=0$ for all $j\in[\ell]\setminus\{i\}$.
--
--   Furthermore
--   $$
--   L_i=U_i-\ell_i^2,\qquad \ell_i(x)=\prod_{j\in[\ell]\setminus\{i\}}\frac{x-x_j}{x_i-x_j},
--   $$
--   where $U_i$ is the majorant of Lemma 4.6 and $\ell_i$ the Lagrange interpolation polynomial.
--
--   The identity lets the proof of Theorem 4.9 evaluate the expectation of $L_i$ under the Gauss rule as $S_i-w_i$.
--
--   Differences from the source:
--
--   - encoding: indices i, j ∈ [ℓ] = {1, …, ℓ} → i, j : Fin ℓ = {0, …, ℓ − 1}; reason: order-preserving reindexing; same statement
--   - encoding: L_i = U_i − ℓ_i², with U_i the majorant of Lemma 4.6 → L = U − (Lagrange.basis univ x i)² for every polynomial U of degree ≤ 2ℓ − 2 with the three properties of Lemma 4.6; reason: conditions 2–3 of Lemma 4.6 determine U_i uniquely (its proof), so this is the paper's U_i without depending on a chosen witness
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Lemma 4.7, p.27 (PDF p.29)

import Mathlib

set_option autoImplicit false

namespace RQCMoments

/-- **Lemma 4.7** (minorant of indicator function) (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Lemma 4.7, p.27, PDF p.29).
For an integer `ℓ > 1` and reals `x₁ < ⋯ < x_ℓ`, for every `i` the indicator `1_{xᵢ}` of
`(−∞, xᵢ]` has a real polynomial minorant `Lᵢ` of degree at most `2ℓ − 2` with
1. `Lᵢ(x) ≤ 1_{xᵢ}(x)` for all real `x`;
2. `Lᵢ(xⱼ) = 1` if `j < i` and `0` if `j ≥ i`;
3. `Lᵢ'(xⱼ) = 0` for all `j ≠ i`.
Furthermore `Lᵢ = Uᵢ − ℓᵢ²`, where `Uᵢ` is the majorant of Lemma 4.6 and
`ℓᵢ(x) = ∏_{j≠i} (x − xⱼ)/(xᵢ − xⱼ)` is the Lagrange interpolation polynomial.

**Formalization Note** The "furthermore" identity is stated for every polynomial `Uᵢ` with the
three properties and degree bound of Lemma 4.6 (they determine `Uᵢ` uniquely), so it does not
depend on a chosen witness. `ℓᵢ` is Mathlib's `Lagrange.basis`. -/
theorem lemma_4_7 (ℓ : ℕ) (hℓ : 1 < ℓ) (x : Fin ℓ → ℝ) (hx : StrictMono x) (i : Fin ℓ) :
    ∃ L : Polynomial ℝ, L.natDegree ≤ 2 * ℓ - 2 ∧
      (∀ t : ℝ, L.eval t ≤ if t ≤ x i then (1 : ℝ) else 0) ∧
      (∀ j, L.eval (x j) = if j < i then 1 else 0) ∧
      (∀ j, j ≠ i → (Polynomial.derivative L).eval (x j) = 0) ∧
      ∀ U : Polynomial ℝ, U.natDegree ≤ 2 * ℓ - 2 →
        (∀ t : ℝ, (if t ≤ x i then (1 : ℝ) else 0) ≤ U.eval t) →
        (∀ j, U.eval (x j) = if j ≤ i then 1 else 0) →
        (∀ j, j ≠ i → (Polynomial.derivative U).eval (x j) = 0) →
        L = U - (Lagrange.basis Finset.univ x i) ^ 2 := by sorry

end RQCMoments
