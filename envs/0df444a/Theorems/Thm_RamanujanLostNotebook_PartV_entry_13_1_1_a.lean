-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartV_entry_13_1_1_a
-- name    : RamanujanLostNotebook.PartV.entry_13_1_1_a
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T18:32:10.819985+00:00
-- url     : https://prove2.me/theorems/93946921-7465-43e6-a8aa-817e3b244454
-- title:
--   Mordell-type integral on page 202 as a sum of two universal mock theta functions
-- statement:
--   Let $n>0$ and $t$ be real with $t/n\pm\frac23\notin\mathbb Z$, $q=e^{-3\pi n}$, $q_1=e^{-\pi/(3n)}$, and $g_3(z;q)=\sum_{m\ge1}\frac{q^{m(m-1)}}{(z;q)_m(q/z;q)_m}$. Then the integrand is integrable on $(0,\infty)$ and $$\frac{2}{\sqrt3}\int_0^\infty\frac{e^{-\pi nx^2/3}\cos\pi tx}{e^{2\pi x/3}+1+e^{-2\pi x/3}}\,dx=q^{2/9}g_3(-e^{\pi t}q^{1/3};q^{2/3})+\frac{e^{-3\pi t^2/(4n)}q_1^{2}}{\sqrt n}\,g_3(-e^{\pi it/n}q_1^{3};q_1^{6}).$$ The right side is the printed $q^{1/18}\sum_{m\ge1}\frac{q^{(2m-1)^2/6}}{(-e^{\pi t}q^{1/3};q^{2/3})_m(-e^{-\pi t}q^{1/3};q^{2/3})_m}+\frac{e^{-3\pi t^2/(4n)}q_1^{1/2}}{\sqrt n}\sum_{m\ge1}\frac{q_1^{3(2m-1)^2/2}}{(-e^{\pi it/n}q_1^3;q_1^6)_m(-e^{-\pi it/n}q_1^3;q_1^6)_m}$. Differs from the printed source: the entry is printed without a range for $n$, $t$; it is stated for real $n>0$, real $t$ (our reading) with the exclusion $t/n\pm\frac23\notin\mathbb Z$ of the book's Theorem 13.1.1, which proves it.
--
--   **Discrepancy from the printed source.** Entry 13.1.1 (pp. 292-293) is printed with 'If q_1 = e^{-π/(3n)} and q = e^{-3πn}' and no range for n or t. We state the first identity for real n > 0 and real t with t/n ± 2/3 ∉ ℤ: the exclusion is the one under which the book proves it (Theorem 13.1.1: Re(t/n) ± 2/3 ∉ ℤ, Re(t/n) ± 4/3 ∉ ℤ, which are two conditions, not four). For real n, t no denominator vanishes, so the pole hypotheses of theorem_13_1_1 are not needed. The version without the exclusion is the separate record entry_13_1_1_a_all_real_t. The two hypergeometric series are written through g_3 of (13.1.7), as the book does on p. 294, and all fractional powers of q, q_1 as exponentials. The domain reading is ours. Revision 2026-10-06 (coordinator's instruction): the first version had no exclusion. The Codex audit rated the unrestricted reading 'ok' on numerical grounds (residuals ≤ 1.1e-51 at three excluded points).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 13, Entry 13.1.1, p. 292.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_ch13_ch13Integrand
import Definitions.Def_RamanujanLostNotebook_PartV_shared_univG3

namespace RamanujanLostNotebook.PartV
theorem entry_13_1_1_a (n t : ℝ) (hn : 0 < n)
    (h1 : ∀ k : ℤ, t / n + 2 / 3 ≠ (k : ℝ))
    (h2 : ∀ k : ℤ, t / n - 2 / 3 ≠ (k : ℝ)) :
    MeasureTheory.IntegrableOn (ch13Integrand (n : ℂ) (t : ℂ)) (Set.Ioi (0 : ℝ)) ∧
      2 / ((Real.sqrt 3 : ℝ) : ℂ) * (∫ x in Set.Ioi (0 : ℝ), ch13Integrand (n : ℂ) (t : ℂ) x) =
        Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ) / 3)) *
          univG3 (-Complex.exp ((Real.pi : ℂ) * (t : ℂ) - (Real.pi : ℂ) * (n : ℂ))) (Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ)))) +
        Complex.exp (-(3 * (Real.pi : ℂ) * (t : ℂ) ^ 2 / (4 * (n : ℂ)))) * Complex.exp (-(2 * (Real.pi : ℂ) / (3 * (n : ℂ)))) /
            ((Real.sqrt n : ℝ) : ℂ) *
          univG3 (-Complex.exp ((Real.pi : ℂ) * Complex.I * (t : ℂ) / (n : ℂ) - (Real.pi : ℂ) / (n : ℂ)))
            (Complex.exp (-(2 * (Real.pi : ℂ) / (n : ℂ)))) := by sorry
end RamanujanLostNotebook.PartV
