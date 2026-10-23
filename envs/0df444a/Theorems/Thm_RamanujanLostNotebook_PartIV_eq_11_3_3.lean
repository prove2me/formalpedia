-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_eq_11_3_3
-- name    : RamanujanLostNotebook.PartIV.eq_11_3_3
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-06T15:33:48.833001+00:00
-- url     : https://prove2.me/theorems/84b0ee51-baf3-4598-8cea-83573eae6e2f
-- title:
--   Under RH, ϑ(x) = Li⁻¹(π(x)) + O(√(n/log n))
-- statement:
--   Assume the Riemann Hypothesis (every zero $\rho$ of $\zeta$ with $0<\mathrm{Re}\,\rho<1$ has $\mathrm{Re}\,\rho=\tfrac12$). Let $n=\pi(x)$ and let $y=\mathrm{Li}^{-1}(n)$ be the solution $y>1$ of $\mathrm{Li}(y)=n$, where $\mathrm{Li}$ is the principal-value integral $\int_0^y dt/\log t$. Then $\vartheta(x)-\mathrm{Li}^{-1}(n)=O(\sqrt{n/\log n})$ as $x\to\infty$.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 11, Entry 11.3.3, p. 252, eq. (11.3.3).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIV_ch11_logIntegral
import Definitions.Def_RamanujanLostNotebook_PartIV_ch11_primeTheta
open MeasureTheory

namespace RamanujanLostNotebook.PartIV
theorem eq_11_3_3
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in Filter.atTop, ∀ y : ℝ, 1 < y →
      logIntegral y = (Nat.primeCounting ⌊x⌋₊ : ℝ) →
      |primeTheta x - y|
        ≤ C * Real.sqrt ((Nat.primeCounting ⌊x⌋₊ : ℝ)
              / Real.log (Nat.primeCounting ⌊x⌋₊ : ℝ)) := by sorry
end RamanujanLostNotebook.PartIV
