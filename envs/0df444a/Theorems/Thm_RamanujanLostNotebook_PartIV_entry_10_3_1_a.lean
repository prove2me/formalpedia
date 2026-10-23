-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_entry_10_3_1_a
-- name    : RamanujanLostNotebook.PartIV.entry_10_3_1_a
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T14:34:54.510356+00:00
-- url     : https://prove2.me/theorems/af01069d-ad8a-43dd-b18d-0b85f50ffdc1
-- title:
--   Cosine Dirichlet series with quadratic phase, even modulus
-- statement:
--   Let $a$ be an even positive integer. Then (absolutely convergent series) $\sum_{n=1}^\infty\frac{\cos(\pi n^2/a)}{n^2}=\frac{\pi^2}{6}-\frac{\pi^2}{\sqrt a}\sum_{r=1}^{a}\frac ra\Big(1-\frac ra\Big)\sin\Big(\frac\pi4+\frac{\pi r^2}{a}\Big)$.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 10, Entry 10.3.1, p. 243, eq. (10.3.1).

import Mathlib

namespace RamanujanLostNotebook.PartIV
theorem entry_10_3_1_a (a : ℕ) (ha : 0 < a) (heven : Even a) :
    HasSum (fun n : ℕ => Real.cos (Real.pi * ((n : ℝ) + 1) ^ 2 / (a : ℝ)) / ((n : ℝ) + 1) ^ 2)
      (Real.pi ^ 2 / 6
        - Real.pi ^ 2 / Real.sqrt (a : ℝ)
          * ∑ r ∈ Finset.Icc 1 a,
              (r : ℝ) / (a : ℝ) * (1 - (r : ℝ) / (a : ℝ))
                * Real.sin (Real.pi / 4 + Real.pi * (r : ℝ) ^ 2 / (a : ℝ))) := by sorry
end RamanujanLostNotebook.PartIV
