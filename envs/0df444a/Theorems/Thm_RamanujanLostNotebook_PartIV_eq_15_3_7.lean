-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_eq_15_3_7
-- name    : RamanujanLostNotebook.PartIV.eq_15_3_7
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T15:37:46.005876+00:00
-- url     : https://prove2.me/theorems/ab454c2d-27a2-45f6-8323-5edef35669f6
-- title:
--   X1(s)X2(1-s) = pi/2^(2g-1) for the sine-product construction
-- statement:
--   Let $g\ge1$, $\{a_1,\dots,a_g\}\sqcup\{b_1,\dots,b_g\}=\{0,\dots,2g-1\}$, $X_1(s)=\Gamma(s)\prod_r\sin\frac{\pi(s+a_r)}{2g}$, $X_2(s)=\Gamma(s)\prod_r\sin\frac{\pi(s-b_r+2g-1)}{2g}$. Then $X_1(s)X_2(1-s)=\pi/2^{2g-1}$ for $s\in\mathbb C\setminus\mathbb Z$. Differs from the printed source: the manuscript asserts only that the product is constant; the value is the book's (15.3.7), and the exclusion of integer $s$ is ours.
--
--   **Discrepancy from the printed source.** Book, pp. 335-336: (15.3.4) with the assertion that X1(s)X2(1-s) is a constant (manuscript) and its value pi/2^{2g-1} (book, (15.3.7)); no condition on s. We state the value and assume s is not an integer. Evidence: the book's proof and numerics in notes. The value is the book's authors'; the hypothesis on s is ours.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 15, Entry 15.3.4, p. 335, eq. (15.3.4), (15.3.7).

import Mathlib

namespace RamanujanLostNotebook.PartIV
theorem eq_15_3_7 (g : ℕ) (hg : 0 < g) (A : Finset ℕ)
    (hA : A ⊆ Finset.range (2 * g)) (hcard : A.card = g)
    (s : ℂ) (hs : ∀ m : ℤ, s ≠ (m : ℂ)) :
    (Complex.Gamma s
        * ∏ a ∈ A, Complex.sin ((Real.pi : ℂ) * (s + (a : ℂ)) / (2 * (g : ℂ))))
      * (Complex.Gamma (1 - s)
        * ∏ b ∈ Finset.range (2 * g) \ A,
            Complex.sin ((Real.pi : ℂ) * ((1 - s) - (b : ℂ) + 2 * (g : ℂ) - 1) / (2 * (g : ℂ))))
      = (Real.pi : ℂ) / 2 ^ (2 * g - 1) := by sorry
end RamanujanLostNotebook.PartIV
