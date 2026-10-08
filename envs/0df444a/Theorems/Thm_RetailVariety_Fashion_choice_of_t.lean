-- Prove2me | Theorems.Thm_RetailVariety_Fashion_choice_of_t
-- name    : RetailVariety.Fashion.choice_of_t
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:54.583989+00:00
-- url     : https://prove2.me/theorems/254bf155-2f6d-4078-bb3f-34905669206a
-- title:
--   Proof of Theorem 3 — there are $t\le r$, $0<\delta\le 1$ with $\sum_{j<t}w_j+\delta w_t=\sum_{j\le r}v_j$
-- statement:
--   Let $v,w\in\mathbb R^n$ be nonnegative and sorted decreasingly, with $v\prec w$. Let $r\le n$ with $\sum_{j=1}^{r}v_j>0$. Then there exist an index $t$ with $1\le t\le r$ and a number $0<\delta\le 1$ such that
--   $$\sum_{j=1}^{t-1}w_j+\delta\,w_t=\sum_{j=1}^{r}v_j.$$
--
--   The first $t-1$ variants of $w$ together with a fraction $\delta$ of variant $t$ carry exactly the preference mass of the $r$ most popular variants of $v$.
--
--   **Formalization Note.** The Lean index `t : Fin n` is the paper's $t-1$ (so `t.val < r`, `A n t.val` $=\{1,\dots,t-1\}$ and `w t` $=w_t$) and `θ` is the paper's $\delta$. The hypothesis $\sum_{j\le r}v_j>0$ is not printed: when the sum is $0$ (e.g. $r=0$) no $\delta>0$ works, and that case of Theorem 3 is immediate.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1506, proof of Theorem 3

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Model
import Definitions.Def_RetailVariety_Fashion_Majorization

namespace RetailVariety.Fashion

/-- p. 1506: if `v ≺ w` (both sorted decreasingly, nonnegative) and `∑_{j=1}^r v_j > 0`, there is
a `t ≤ r` and `0 < δ ≤ 1` with `∑_{j=1}^{t−1} w_j + δ w_t = ∑_{j=1}^r v_j`. In Lean, `t : Fin n`
is the paper's `t − 1` (so `t.val < r`, `A n t` is `{1, …, t − 1}` and `w t` is `w_t`), and `θ`
is the paper's `δ`. -/
theorem choice_of_t {n : ℕ} (v w : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j)
    (hva : Antitone v) (hwa : Antitone w) (hvw : Majorized v w) (r : ℕ) (hr : r ≤ n)
    (hpos : 0 < ∑ j ∈ RetailVariety.Statics.A n r, v j) :
    ∃ t : Fin n, t.val < r ∧ ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
      ∑ j ∈ RetailVariety.Statics.A n t.val, w j + θ * w t = ∑ j ∈ RetailVariety.Statics.A n r, v j := by sorry

end RetailVariety.Fashion
