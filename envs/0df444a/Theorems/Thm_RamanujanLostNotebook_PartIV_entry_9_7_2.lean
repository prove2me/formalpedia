-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_entry_9_7_2
-- name    : RamanujanLostNotebook.PartIV.entry_9_7_2
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-06T16:57:08.568989+00:00
-- url     : https://prove2.me/theorems/8ba08506-8e58-4eef-814a-bce70ce4f3bb
-- title:
--   sum d'(n)/sqrt n = zeta(1/2)^2 - C
-- statement:
--   Let $d'(n)=d(n)-2\gamma-\log n$ and $C=\zeta(\tfrac12)\{\tfrac32\gamma-\tfrac14\pi-\tfrac12\log(8\pi)\}$. Then $\lim_{N\to\infty}\sum_{n=1}^N\dfrac{d'(n)}{\sqrt n}=\zeta^2(\tfrac12)-C$.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 9, Entry 9.7.2, p. 231, eq. (9.7.7), (9.7.8).

import Mathlib

namespace RamanujanLostNotebook.PartIV
theorem entry_9_7_2 :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.Icc 1 N,
          (((Nat.divisors n).card : ℝ) - 2 * Real.eulerMascheroniConstant - Real.log (n : ℝ)) / Real.sqrt (n : ℝ))
      Filter.atTop
      (nhds ((riemannZeta (1 / 2 : ℂ)).re ^ 2 - ((riemannZeta (1 / 2 : ℂ)).re * (3 / 2 * Real.eulerMascheroniConstant - Real.pi / 4 - Real.log (8 * Real.pi) / 2)))) := by sorry
end RamanujanLostNotebook.PartIV
