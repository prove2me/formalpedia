-- Prove2me | Theorems.Thm_PorteusSS_CK_sS_structure
-- name    : PorteusSS.CK_sS_structure
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:53:54.429641+00:00
-- url     : https://prove2.me/theorems/ac70455c-3d20-4ff7-8c4a-4dfdc54aba57
-- title:
--   Lemma 1 — a $C(K)$ function has the $(s,S)$ shape
-- statement:
--   Let $K \ge 0$ and let $f \in C(K)$, i.e. $f$ is continuous and lies in $C_a(K)$ for some $a$. Then there exist real numbers $s$ and $S$ such that
--
--   1. $s \le S$,
--   2. $f(S) \le f(x)$ for all $x \in \mathbb R$,
--   3. $f(x) > f(S) + K$ for $x < s$,
--   4. $f$ is nonincreasing on $(-\infty, s)$, and
--   5. $f(x) \le f(y) + K$ for $s \le x \le y$.
--
--   Consequently
--   $$ \inf_{y \ge x} \big[K\,\delta(y - x) + f(y)\big] = \begin{cases} K + f(S), & x < s,\\ f(x), & x \ge s,\end{cases} $$
--   where $\delta$ is the Heaviside function, so an $(s,S)$ rule is optimal for a single setup cost $K$ and period cost $f$. These are exactly the properties of $C(K)$ functions used to characterize the optimal policy in the inventory model.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), p. 414, Lemma 1 (proof p. 424)

import Mathlib
import Definitions.Def_PorteusSS_Functions

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Lemma 1 (p. 414). If `f ∈ C(K)`, there are reals `s ≤ S` such that `S` minimizes `f`,
`f x > f S + K` for `x < s`, `f` is nonincreasing on `(-∞, s)`, and `f x ≤ f y + K` for
`s ≤ x ≤ y`. -/
theorem CK_sS_structure (K : ℝ) (f : ℝ → ℝ) (hf : CK K f) :
    ∃ s S : ℝ, s ≤ S ∧ (∀ x : ℝ, f S ≤ f x) ∧ (∀ x : ℝ, x < s → f S + K < f x) ∧
      AntitoneOn f (Iio s) ∧ (∀ x y : ℝ, s ≤ x → x ≤ y → f x ≤ f y + K) := by sorry

end PorteusSS
