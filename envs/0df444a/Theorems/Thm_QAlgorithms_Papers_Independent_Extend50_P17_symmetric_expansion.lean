-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_symmetric_expansion
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.symmetric_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:01:29.506987+00:00
-- url     : https://prove2.me/theorems/4794bc95-b44e-405f-9e30-5a7d4642fe13
-- title:
--   Unnumbered Eqs.(56)–(57): symmetric-polynomial expansion of the bound
-- statement:
--   Fix integers $d,k\ge1$ and put $x_s=(d^2+N-s-1)^{-1}$ for $s=0,\ldots,k-1$. Let $e_l(x)$ be the elementary symmetric polynomial, the sum of products over distinct $l$-element subsets, and put $S(N)=\sum_{l=0}^k(-1)^l(d^2-1)^l e_l(x)$. For $2k\le N$,
--
--   $$F_d(N,k)\ge\prod_{s=0}^{k-1}(1-(d^2-1)x_s)=S(N).$$
--
--   For fixed $d,k$ there are $C>0,N_0$ such that for all $N\ge N_0$,
--
--   $$\left|S(N)-\left(1-\sum_{s=0}^{k-1}(d^2-1)x_s\right)\right|\le C/N^2.$$
--
--   The source's description as completely symmetric polynomials and its weak inequality in Eq. (55) are corrected to the elementary polynomials required by the product expansion. This is an alternative lower bound, not an exact physical fidelity formula.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 12, Unnumbered Eqs.(56)–(57): symmetric-polynomial expansion of the bound

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.12, Eqs.(56)–(57): corrected elementary expansion and fixed-k O(N^-2) remainder.
Printed (55) includes repeated indices in S_2; distinct subsets are required by
the product expansion (56), so elementary symmetric coefficients are used. -/
theorem symmetric_expansion (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) :
    (∀ N : ℕ, 2*k ≤ N →
      symmetricBound d N k ≤ mpbtFidelity d N k ∧
      (∏ s : Fin k, (1 - ((d : ℝ)^2 - 1) * boundVariables d N k s)) =
        symmetricBound d N k) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N ≥ N0,
      |symmetricBound d N k -
        (1 - ∑ s : Fin k, ((d : ℝ)^2 - 1) * boundVariables d N k s)| ≤
        C / (N : ℝ)^2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
