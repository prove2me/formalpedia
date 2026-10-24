-- Prove2me | Theorems.Thm_SKAlgorithm_Qudit_eq_4
-- name    : SKAlgorithm.Qudit.eq_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:55.533573+00:00
-- url     : https://prove2.me/theorems/9c19e1e0-01a0-4370-8034-9efc6adac4e6
-- title:
--   Eq. (4), p. 7 — closed form of the accuracies ε_n
-- statement:
--   Let $c > 0$ and $\epsilon_0 > 0$, and let $\epsilon_n = c\, \epsilon_{n-1}^{3/2}$ for $n \ge 1$ (Eq. (1)). Then for every $n \ge 0$
--   $$\epsilon_n = \frac{1}{c^2} \left(\epsilon_0 c^2\right)^{(3/2)^n} .$$
--
--   In particular $\epsilon_n \to 0$ doubly exponentially in $n$ when $\epsilon_0 c^2 < 1$, which is what makes the number of recursion levels logarithmic in $\log(1/\epsilon)$.
--
--   **Formalization Note.** $c$ is the paper's $c_{\mathrm{approx}}$; powers with non-integer exponents are real powers of positive reals.
-- source:
--   Dawson and Nielsen, The Solovay-Kitaev algorithm, arXiv:quant-ph/0505030v2, p. 7, Eq. (4)

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix
open QAlgorithms

namespace SKAlgorithm.Qudit

theorem eq_4 (c ε₀ : ℝ) (hc : 0 < c) (hε₀ : 0 < ε₀) (n : ℕ) :
    epsSeq c ε₀ n = 1 / c ^ 2 * (ε₀ * c ^ 2) ^ (((3 : ℝ) / 2) ^ n) := by sorry

end SKAlgorithm.Qudit
