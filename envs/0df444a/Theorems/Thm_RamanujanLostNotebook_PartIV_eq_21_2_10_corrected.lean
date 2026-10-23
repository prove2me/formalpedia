-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_eq_21_2_10_corrected
-- name    : RamanujanLostNotebook.PartIV.eq_21_2_10_corrected
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T14:37:46.137097+00:00
-- url     : https://prove2.me/theorems/f45e0044-e207-47a6-9c6d-e829d32e75aa
-- title:
--   Number of sums of two squares below x (Landau–Ramanujan, leading term)
-- statement:
--   Let $B(x)$ be the number of integers $<x$ of the form $a^2+b^2$ with $a,b$ positive integers, and $P=\prod_{p\equiv3\ (\mathrm{mod}\ 4)}(1-p^{-2})$ (an absolutely convergent product). Then $\displaystyle\lim_{x\to\infty}\frac{B(x)\sqrt{\log x}}{x}=\frac1{\sqrt{2P}}$. Differs from the printed source: the manuscript has the constant $\sqrt{2P}$ and an error term $O(x^{1/2+\varepsilon})$; the book's authors say the constant should be the reciprocal and the error term is wrong; we state the leading asymptotic with the reciprocal constant.
--
--   **Discrepancy from the printed source.** Book p. 410, (21.2.10)–(21.2.11): B(x) = C∫dx/√(log x) + O(x^{1/2+ε}), C = √(2(1−1/3²)(1−1/7²)(1−1/11²)(1−1/19²)…). The book (p. 411): the error term is incorrect and the correct constant is the reciprocal of the printed one. We state lim B(x)√(log x)/x = 1/√(2P). Correction made by the book's authors; numerically 1/√(2P) = 0.764224 matches the Landau–Ramanujan constant and the count ratio is 0.797 at x = 1e7 (trend only). The Codex audit confirms from a 220 dpi render that the print has C = √(2P) and that the book calls for the reciprocal and rejects the error term.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 21, Entry (21.2.10), p. 410, eq. (21.2.10), (21.2.11).

import Mathlib

namespace RamanujanLostNotebook.PartIV
theorem eq_21_2_10_corrected :
    ∃ P : ℝ,
      HasProd
        (fun p : Nat.Primes =>
          if (p : ℕ) % 4 = 3 then 1 - 1 / ((p : ℕ) : ℝ) ^ 2 else 1) P ∧
      Filter.Tendsto
        (fun x : ℝ =>
          (Set.ncard {k : ℕ | 0 < k ∧ (k : ℝ) < x ∧
            ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ k = a ^ 2 + b ^ 2} : ℝ)
            * Real.sqrt (Real.log x) / x)
        Filter.atTop (nhds (1 / Real.sqrt (2 * P))) := by sorry
end RamanujanLostNotebook.PartIV
