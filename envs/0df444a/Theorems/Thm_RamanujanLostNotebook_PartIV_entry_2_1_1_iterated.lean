-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_entry_2_1_1_iterated
-- name    : RamanujanLostNotebook.PartIV.entry_2_1_1_iterated
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T15:19:23.139984+00:00
-- url     : https://prove2.me/theorems/ef10b7db-bbdb-4332-8bb5-82f4d1cb8526
-- title:
--   Ramanujan's first Bessel-series identity, iterated in the order written (sum over n first)
-- statement:
--   Let $F(y)=\lfloor y\rfloor$ for non-integral $y$ and $F(y)=y-\tfrac12$ for integral $y$. For $x>0$, $0<\theta<1$ and each $m\ge1$ the series $a_m=\sum_{n\ge0}\Big\{\frac{J_1(4\pi\sqrt{m(n+\theta)x})}{\sqrt{m(n+\theta)}}-\frac{J_1(4\pi\sqrt{m(n+1-\theta)x})}{\sqrt{m(n+1-\theta)}}\Big\}$ converges (limit of partial sums), the series $\sum_{m\ge1}a_m$ converges (limit of partial sums), and $\sum_{n\ge1}F(x/n)\sin(2\pi n\theta)=\pi x(\tfrac12-\theta)-\tfrac14\cot(\pi\theta)+\tfrac12\sqrt x\sum_{m\ge1}a_m$. The left side is a finite sum ($n\le x$). Differs from the printed source: (2.1.5) is printed as a double series with no order of summation; this statement fixes the order (sum over $n$ for each $m$, then over $m$) with both sums as ordinary limits of partial sums, the interpretation proved in Section 2.2 of the book.
--
--   **Discrepancy from the printed source.** Book p. 8 (2.1.5): a double series with no summation mode specified. Stated here: the order n first (for each m), then m, both as ordinary iterated limits of partial sums. This is the Section 2.2 interpretation proved in the book (pp. 15-56). Who: the choice of reading is the book's; the audit asked for this disclosure. Evidence for the identity in this reading: the book's proof; our numerics are a trend check (2 digits raw, 4-5 in the mean), numerical evidence, not a proof.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 2, Entry 2.1.1, p. 8, eq. (2.1.5).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIV_shared_besselJ
import Definitions.Def_RamanujanLostNotebook_PartIV_ch02_floorHalf

namespace RamanujanLostNotebook.PartIV
theorem entry_2_1_1_iterated (x θ : ℝ) (hx : 0 < x) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ a : ℕ → ℝ,
      (∀ m : ℕ, 1 ≤ m →
        Filter.Tendsto
          (fun N : ℕ => ∑ n ∈ Finset.range N,
            ((besselJ 1 (4 * Real.pi * Real.sqrt ((m : ℝ) * ((n : ℝ) + θ) * x))
                  / Real.sqrt ((m : ℝ) * ((n : ℝ) + θ)))
              - (besselJ 1 (4 * Real.pi * Real.sqrt ((m : ℝ) * ((n : ℝ) + 1 - θ) * x))
                  / Real.sqrt ((m : ℝ) * ((n : ℝ) + 1 - θ)))))
          Filter.atTop (nhds (a m))) ∧
      Filter.Tendsto
        (fun M : ℕ => Real.pi * x * (1 / 2 - θ) - 1 / 4 * (Real.cos (Real.pi * θ) / Real.sin (Real.pi * θ))
          + 1 / 2 * Real.sqrt x * ∑ m ∈ Finset.Icc 1 M, a m)
        Filter.atTop
        (nhds (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          floorHalf (x / (n : ℝ)) * Real.sin (2 * Real.pi * (n : ℝ) * θ))) := by sorry
end RamanujanLostNotebook.PartIV
