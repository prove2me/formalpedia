-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_11_13
-- name    : RamanujanNotebooks.entry_11_13
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-07T03:31:45.099007+00:00
-- url     : https://prove2.me/theorems/d564dab0-1ee1-4533-b750-3d3b80dfd414
-- title:
--   Clausen's formula: the square of 2F1(-α, -β; γ + 1/2; x) with α + β + γ = 0 as a 3F2
-- statement:
--   Let $\alpha+\beta+\gamma=0$ with $\gamma+\frac12$ and $2\gamma$ not $0$ or a negative integer, and $|x|<1$. Then $${}_2F_1(-\alpha,-\beta;\gamma+\tfrac12;x)^2={}_3F_2(-2\alpha,-2\beta,\gamma;\gamma+\tfrac12,2\gamma;x).$$ Differs from the printed source: the book prints the formula with no region of validity and no condition on the parameters; we state it for |x| < 1 with the lower parameters γ + 1/2 and 2γ not 0 or a negative integer. Conditions supplied by us.
--
--   **Discrepancy from the printed source.** Book, p. 58: the formula is printed with the single condition α + β + γ = 0. Our statement: the book prints the formula with no region of validity and no condition on the parameters; we state it for |x| < 1 with the lower parameters γ + 1/2 and 2γ not 0 or a negative integer. Conditions supplied by us.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part II (Springer, 1989), Chapter 11, Entry 13, p. 58.

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_hyp2F1
import Definitions.Def_RamanujanNotebooks_shared_hypPFQ

namespace RamanujanNotebooks
theorem entry_11_13 (α β γ x : ℂ) (h : α + β + γ = 0)
    (hγ : ∀ w ∈ ([γ + 1 / 2, 2 * γ] : List ℂ), ∀ j : ℕ, w ≠ -(j : ℂ)) (hx : ‖x‖ < 1) :
    hyp2F1 (-α) (-β) (γ + 1 / 2) x ^ 2 = hypPFQ [-2 * α, -2 * β, γ] [γ + 1 / 2, 2 * γ] x := by sorry
end RamanujanNotebooks
