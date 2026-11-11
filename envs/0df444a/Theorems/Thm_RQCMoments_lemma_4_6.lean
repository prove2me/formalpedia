-- Prove2me | Theorems.Thm_RQCMoments_lemma_4_6
-- name    : RQCMoments.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:08:16.65085+00:00
-- url     : https://prove2.me/theorems/109864ac-5548-4c59-bfbf-1acf2a1f6a9f
-- title:
--   Lemma 4.6 — polynomial majorant $U_i$ of the indicator of $(-\infty,x_i]$
-- statement:
--   Let $\ell>1$ be an integer and $x_1<x_2<\dots<x_\ell$ real numbers. For $i\in[\ell]$ write $1_{x_i}$ for the indicator function of $(-\infty,x_i]$. Then for every $i$ there is a real polynomial $U_i$ of degree at most $2\ell-2$ such that
--   1. $U_i(x)\ge 1_{x_i}(x)$ for all $x\in\mathbb R$;
--   2. $U_i(x_j)=1$ if $j\le i$ and $U_i(x_j)=0$ if $j>i$;
--   3. $U_i'(x_j)=0$ for all $j\in[\ell]\setminus\{i\}$.
--
--   Together with Lemma 4.7 this gives the polynomial bracketing of the distribution function at quadrature nodes (Lemma 4.8, Theorem 4.9).
--
--   Differences from the source:
--
--   - encoding: indices i, j ∈ [ℓ] = {1, …, ℓ} → i, j : Fin ℓ = {0, …, ℓ − 1}; reason: order-preserving reindexing; same statement
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Lemma 4.6 and the definition of 1_{x_i} above it, p.27 (PDF p.29)

import Mathlib

set_option autoImplicit false

namespace RQCMoments

/-- **Lemma 4.6** (majorant of indicator function) (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Lemma 4.6, p.27, PDF p.29).
For an integer `ℓ > 1` and reals `x₁ < ⋯ < x_ℓ`, for every `i` the indicator `1_{xᵢ}` of
`(−∞, xᵢ]` has a real polynomial majorant `Uᵢ` of degree at most `2ℓ − 2` with
1. `Uᵢ(x) ≥ 1_{xᵢ}(x)` for all real `x`;
2. `Uᵢ(xⱼ) = 1` if `j ≤ i` and `Uᵢ(xⱼ) = 0` if `j > i`;
3. `Uᵢ'(xⱼ) = 0` for all `j ≠ i`. -/
theorem lemma_4_6 (ℓ : ℕ) (hℓ : 1 < ℓ) (x : Fin ℓ → ℝ) (hx : StrictMono x) (i : Fin ℓ) :
    ∃ U : Polynomial ℝ, U.natDegree ≤ 2 * ℓ - 2 ∧
      (∀ t : ℝ, (if t ≤ x i then (1 : ℝ) else 0) ≤ U.eval t) ∧
      (∀ j, U.eval (x j) = if j ≤ i then 1 else 0) ∧
      (∀ j, j ≠ i → (Polynomial.derivative U).eval (x j) = 0) := by sorry

end RQCMoments
