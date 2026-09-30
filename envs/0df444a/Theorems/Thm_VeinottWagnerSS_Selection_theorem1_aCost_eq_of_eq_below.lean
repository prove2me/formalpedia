-- Prove2me | Theorems.Thm_VeinottWagnerSS_Selection_theorem1_aCost_eq_of_eq_below
-- name    : VeinottWagnerSS.Selection.theorem1_aCost_eq_of_eq_below
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:07:41.944897+00:00
-- url     : https://prove2.me/theorems/f8ea52fd-ffc9-49d4-b5bb-cb341cdd0d47
-- title:
--   Theorem 1 — two (s, S) policies with equal average cost below $s'$ have equal average cost everywhere
-- statement:
--   Let $0 \le \alpha < 1$ and consider two stationary $(s, S)$ policies $(s, S)$ and $(s', S')$ (so $s \le S$, $s' \le S'$) with $s \le s'$. Let $a_\alpha(x \mid s, S) = (1-\alpha) f(x \mid s, S)$ be the equivalent average cost per period from the starting stock $X_1 = x$. If
--   $$a_\alpha(x \mid s, S) = a_\alpha(x \mid s', S') \qquad \text{for all } x < s',$$
--   then
--   $$a_\alpha(x \mid s, S) = a_\alpha(x \mid s', S') \qquad \text{for all integers } x.$$
--
--   The theorem reduces the comparison of two policies on all starting stocks to the comparison on the finitely many stocks $s \le x < s'$ that matter in Step iii of the paper's algorithm, and it is one of the two ingredients of Theorem 2.
--
--   **Formalization Note** The model's standing assumptions (convexity and coercivity of $G_\alpha$, $K \ge 0$, finite mean demand) are fields of `Model`; the statement is kept under them as in the paper, although it does not need them.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 542, Theorem 1 (proof: Appendix §3, pp. 550-551)

import Mathlib
import Definitions.Def_VeinottWagnerSS_Selection_Model

namespace VeinottWagnerSS.Selection

/-- Veinott & Wagner (1965), Theorem 1, p. 542: if `0 ≤ α < 1`, if the two `(s, S)` policies
`(s, S)`, `(s', S')` satisfy `s ≤ s'`, and if `a_α(x | s, S) = a_α(x | s', S')` for every
`x < s'`, then `a_α(x | s, S) = a_α(x | s', S')` for all `x`. -/
theorem theorem1_aCost_eq_of_eq_below (M : Model) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (s S s' S' : ℤ) (hsS : s ≤ S) (hsS' : s' ≤ S') (hss' : s ≤ s')
    (heq : ∀ x : ℤ, x < s' → aCost M α s S x = aCost M α s' S' x) :
    ∀ x : ℤ, aCost M α s S x = aCost M α s' S' x := by sorry

end VeinottWagnerSS.Selection
