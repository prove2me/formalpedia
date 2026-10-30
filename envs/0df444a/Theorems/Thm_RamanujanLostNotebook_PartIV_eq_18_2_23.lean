-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIV_eq_18_2_23
-- name    : RamanujanLostNotebook.PartIV.eq_18_2_23
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-06T15:25:08.266262+00:00
-- url     : https://prove2.me/theorems/85fa9eb0-8f01-406a-b6db-6ca47174b5e9
-- title:
--   Gaussian-sech reciprocity
-- statement:
--   Let $\alpha,\beta>0$ with $\alpha\beta=\pi$. Then $\sqrt\alpha\int_0^\infty \frac{e^{-(\alpha x)^2}}{\cosh\pi x}\,dx=\sqrt\beta\int_0^\infty \frac{e^{-(\beta x)^2}}{\cosh\pi x}\,dx$. Differs from the printed source: the print gives only the product condition and does not say $\alpha,\beta>0$; positivity is made explicit as a domain convention for the printed real square roots (ours; not a numerically discovered correction).
--
--   **Discrepancy from the printed source.** Book, p. 368, (18.2.23): the display has the condition on alpha*beta and the real square roots sqrt(alpha), sqrt(beta), but does not print alpha > 0, beta > 0. The Lean statement assumes 0 < alpha and 0 < beta. This is an explicit domain convention for the printed real square roots, not a numerically discovered correction; it keeps Real.sqrt of a negative number out of the statement. The audit's independent 42-digit check agrees with ours at alpha = 0.8, 3.1, 0.05. Convention chosen by us.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013, Chapter 18, Entry 18.2.23, p. 368, eq. (18.2.23).

import Mathlib
open MeasureTheory

namespace RamanujanLostNotebook.PartIV
theorem eq_18_2_23 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hαβ : α * β = Real.pi) :
    Real.sqrt α * (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-(α * x) ^ 2) / Real.cosh (Real.pi * x))
      = Real.sqrt β * (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-(β * x) ^ 2) / Real.cosh (Real.pi * x)) := by sorry
end RamanujanLostNotebook.PartIV
