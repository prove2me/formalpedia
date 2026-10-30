-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_section_9_6_zeta_complex
-- name    : RamanujanLostNotebook.PartIV.section_9_6_zeta_complex
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-22T09:17:29.825027+00:00
-- url     : https://prove2.me/theorems/ed154033-f889-42b8-a399-b9d7eda83e42
-- title:
--   zeta(s) = 1/(s-1) + gamma + o(1) as complex s -> 1 with Re s > 1
-- statement:
--   Let $\gamma$ be Euler's constant. For complex $s$ with $\operatorname{Re}s>1$, as $s\to1$: $\sum_{n\ge1}n^{-s}=\dfrac1{s-1}+\gamma+o(1)$.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 9, Section 9.6, first formula, p. 227, unnumbered, p. 227.

import Mathlib

namespace RamanujanLostNotebook.PartIV
theorem section_9_6_zeta_complex :
    Filter.Tendsto (fun s : ℂ => (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s) - 1 / (s - 1))
      (nhdsWithin (1 : ℂ) {s : ℂ | 1 < s.re}) (nhds (Real.eulerMascheroniConstant : ℂ)) := by sorry
end RamanujanLostNotebook.PartIV
