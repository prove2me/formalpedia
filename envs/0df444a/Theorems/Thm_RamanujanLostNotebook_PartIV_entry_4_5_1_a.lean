-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_entry_4_5_1_a
-- name    : RamanujanLostNotebook.PartIV.entry_4_5_1_a
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T12:24:22.580988+00:00
-- url     : https://prove2.me/theorems/1955e716-166b-49c8-81b9-77e47add5274
-- title:
--   Ramanujan's two-sided sixth-root bound for the gamma function
-- statement:
--   For real $x\ge 1$: $\sqrt{\pi}\left(\frac{x}{e}\right)^x\left(8x^3+4x^2+x+\frac{1}{100}\right)^{1/6}<\Gamma(x+1)<\sqrt{\pi}\left(\frac{x}{e}\right)^x\left(8x^3+4x^2+x+\frac{1}{30}\right)^{1/6}$. Differs from the printed source: the entry is printed for $x\ge 0$; we state the range $x\ge 1$ covered by the book's proof (restriction ours); also the Location Guide's listing of this entry under manuscript page 199 appears to be a slip for page 339.
--
--   **Discrepancy from the printed source.** Book, pp. 117-118, Entry 4.5.1 / (4.5.2), prints the inequality for x >= 0. We state it for x >= 1, the range covered by the proof presented in the book (Karatsuba; the part 1 < x <= 4.21 is itself referred to Karatsuba's computations); 0 < x < 1 is credited to Alzer without proof. Numerically the inequality also holds on (0,1), so this is a restriction to what the book proves, not a claim that the print is wrong. The restriction is ours. Separately, the book's Location Guide (p. 413) lists Entry 4.5.1 under manuscript page 199 as well as 339; the chapter text places it on page 339, so the page-199 line appears to be a slip (our reading).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 4, Entry 4.5.1, p. 118, eq. (4.5.2).

import Mathlib

namespace RamanujanLostNotebook.PartIV
theorem entry_4_5_1_a (x : ℝ) (hx : 1 ≤ x) :
    Real.sqrt Real.pi * (x / Real.exp 1) ^ x *
        (8 * x ^ (3 : ℕ) + 4 * x ^ (2 : ℕ) + x + 1 / 100) ^ ((1 : ℝ) / 6) <
      Real.Gamma (x + 1) ∧
    Real.Gamma (x + 1) <
      Real.sqrt Real.pi * (x / Real.exp 1) ^ x *
        (8 * x ^ (3 : ℕ) + 4 * x ^ (2 : ℕ) + x + 1 / 30) ^ ((1 : ℝ) / 6) := by sorry
end RamanujanLostNotebook.PartIV
