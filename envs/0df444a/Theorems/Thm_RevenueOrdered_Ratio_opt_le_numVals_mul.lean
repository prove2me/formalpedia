-- Prove2me | Theorems.Thm_RevenueOrdered_Ratio_opt_le_numVals_mul
-- name    : RevenueOrdered.Ratio.opt_le_numVals_mul
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:48:09.045518+00:00
-- url     : https://prove2.me/theorems/fca3bdab-fbea-40ab-9127-5816d1d1016d
-- title:
--   Theorem 3.1 — revenue-ordered assortments are a 1/k-approximation
-- statement:
--   Let $\mathcal P$ be a regular discrete choice model on a finite nonempty set of products $\mathcal C$, let $r:\mathcal C\to\mathbb R_{>0}$, and let $k$ be the number of distinct values of $r$. Let $\mathrm{OPT}$ be the optimal revenue of the assortment problem and $\mathrm{RO}=\max_{i\in[k]}\operatorname{rev}(S_i)$ the revenue of the best revenue-ordered assortment. Then revenue-ordered assortments approximate the optimum revenue to within a factor of $1/k$:
--   $$
--   \mathrm{OPT}\;\le\;k\cdot\mathrm{RO}.
--   $$
--
--   This is the first and simplest guarantee of the paper, bound (A) of its introduction. It depends only on the number of distinct prices, not on the choice model.
--
--   **Formalization Note** "Approximates to within a factor of $1/k$" means $\mathrm{RO}\ge\frac1k\mathrm{OPT}$; since $k\ge1$ it is stated in the equivalent product form, without a division.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 7, Theorem 3.1

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered

namespace RevenueOrdered.Ratio

/-- Theorem 3.1 (p. 7): revenue-ordered assortments approximate the optimum revenue to within
a factor of `1/k`, i.e. `OPT ≤ k · RO`. -/
theorem opt_le_numVals_mul {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    (P : C → Finset C → ℝ) (hP : IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x) :
    opt P r ≤ (numVals r : ℝ) * roValue P r := by sorry

end RevenueOrdered.Ratio
