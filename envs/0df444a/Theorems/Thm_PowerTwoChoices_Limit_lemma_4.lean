-- Prove2me | Theorems.Thm_PowerTwoChoices_Limit_lemma_4
-- name    : PowerTwoChoices.Limit.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:59.697888+00:00
-- url     : https://prove2.me/theorems/c1023577-bae2-4d54-99a7-02fb23a903d0
-- title:
--   Lemma 4 — the drift of the supermarket system is $L_1$-Lipschitz with constant $2+2d\lambda$
-- statement:
--   Let $d\ge2$ and $0<\lambda<1$, and let $F(x)=(F_i(x))_{i\ge1}$ with $F_i(x)=\lambda(x_{i-1}^d-x_i^d)-(x_i-x_{i+1})$ be the right-hand side of the limiting supermarket system (1). For any two states $x$ and $y$ (in particular $0\le x_i,y_i\le1$),
--   $$\sum_{i=1}^\infty|F_i(x)-F_i(y)|\le(2+2d\lambda)\sum_{i=0}^\infty|x_i-y_i| .$$
--
--   This is the Lipschitz condition of Kurtz's theorem, which connects the finite supermarket system with its deterministic limit.
--
--   **Formalization Note.** The paper states "The supermarket model satisfies the Lipschitz condition" $|F(x)-F(y)|\le M|x-y|$; the constant $M=2+2d\lambda$ and the $L_1$ norm are those of its proof. Both sums are computed in $[0,\infty]$, so no summability hypothesis is needed.
-- source:
--   Mitzenmacher, The Power of Two Choices in Randomized Load Balancing, IEEE Trans. Parallel Distrib. Syst. 12(10), 2001, p. 1103, Lemma 4 and its proof

import Mathlib
import Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem

open scoped ENNReal
open Filter Topology

namespace PowerTwoChoices.Limit

/-- Lemma 4 (Mitzenmacher 2001, p. 1103), with the constant of its proof. For states `x, y`
(so `0 ≤ x_i, y_i ≤ 1`), the drift `F` of the limiting system satisfies the `ℓ¹` Lipschitz
bound `∑_{i ≥ 1} |F_i(x) - F_i(y)| ≤ (2 + 2dλ) ∑_{i ≥ 0} |x_i - y_i|` (sums in `[0, ∞]`). -/
theorem lemma_4 (lam : ℝ) (d : ℕ) (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (x y : ℕ → ℝ) (hx : IsState x) (hy : IsState y) :
    (∑' i : ℕ, if 1 ≤ i then ENNReal.ofReal |drift lam d x i - drift lam d y i| else 0) ≤
      ENNReal.ofReal (2 + 2 * d * lam) * ∑' i : ℕ, ENNReal.ofReal |x i - y i| := by sorry

end PowerTwoChoices.Limit
