-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartV_entry_12_1_1
-- name    : RamanujanLostNotebook.PartV.entry_12_1_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T19:26:51.413779+00:00
-- url     : https://prove2.me/theorems/2c541680-075b-420d-991e-9df3b77819e6
-- title:
--   Mordell integral transformation of phi_10 and psi_10, first formula
-- statement:
--   For real $n>0$, $\displaystyle\int_0^\infty\frac{e^{-\pi nx^2}}{\cosh\frac{2\pi x}{\sqrt5}+\frac{1+\sqrt5}{4}}\,dx+\frac{1}{\sqrt n}e^{\pi/(5n)}\psi_{10}(-e^{-\pi/n})=\sqrt{\frac{5+\sqrt5}{2}}\,e^{-\pi n/5}\phi_{10}(-e^{-\pi n})-\frac{\sqrt5+1}{2\sqrt n}e^{-\pi/(5n)}\phi_{10}(-e^{-\pi/n})$, where $\phi_{10}(q)=\sum_{n\ge0}q^{n(n+1)/2}/(q;q^2)_{n+1}$ and $\psi_{10}(q)=\sum_{n\ge0}q^{(n+1)(n+2)/2}/(q;q^2)_{n+1}$ are tenth order mock theta functions; the integrand is integrable on $(0,\infty)$ (stated as part of the conclusion). Manuscript claim (Lost Notebook p. 9); restated in the book as Entry 12.3.1.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 12, Entry 12.1.1, p. 249, eq. (12.1.3).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockPhi10
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockPsi10
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mordellTenth
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

namespace RamanujanLostNotebook.PartV
theorem entry_12_1_1 (n : ℝ) (hn : 0 < n) :
    MeasureTheory.IntegrableOn
        (fun x : ℝ => Real.exp (-(Real.pi * n * x ^ 2)) /
          (Real.cosh (2 * Real.pi * x / Real.sqrt 5) + (1 + Real.sqrt 5) / 4))
        (Set.Ioi (0 : ℝ)) ∧
      ((mordellTenth ((1 + Real.sqrt 5) / 4) n : ℝ) : ℂ) +
          ((1 / Real.sqrt n * Real.exp (Real.pi / (5 * n)) : ℝ) : ℂ) *
            mockPsi10 (-((Real.exp (-(Real.pi / n)) : ℝ) : ℂ)) =
        ((Real.sqrt ((5 + Real.sqrt 5) / 2) * Real.exp (-(Real.pi * n / 5)) : ℝ) : ℂ) *
            mockPhi10 (-((Real.exp (-(Real.pi * n)) : ℝ) : ℂ)) -
          (((Real.sqrt 5 + 1) / (2 * Real.sqrt n) * Real.exp (-(Real.pi / (5 * n))) : ℝ) : ℂ) *
            mockPhi10 (-((Real.exp (-(Real.pi / n)) : ℝ) : ℂ)) := by sorry
end RamanujanLostNotebook.PartV
