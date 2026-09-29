-- Prove2me | Theorems.Thm_PorteusSS_valueFn_le_add_cost
-- name    : PorteusSS.valueFn_le_add_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:57:45.39067+00:00
-- url     : https://prove2.me/theorems/a50985da-6e44-4fdc-b29a-2cc7ae3950af
-- title:
--   Lemma 2 — $f_n(x) \le f_n(y) + c(y - x)$ for $x \le y$
-- statement:
--   In the inventory model of §§II–III under its standing assumptions, let $n \ge 1$ and assume, as the paper does for every function it considers, that $f_n$ is real valued, i.e. each infimum $\inf_{w \ge x}\{c(w - x) + h_n(w)\}$ is over a set bounded below. Then for all $x \le y$,
--   $$ f_n(x) \le f_n(y) + c(y - x). $$
--
--   The inequality says that the optimal cost can only benefit from a lower starting inventory by at most the cost of ordering the difference; combined with (1) it shows that $f_n + \kappa\cdot$ is non-$K_\kappa$-decreasing for $\kappa \in C$, which is condition (iii) of Lemma 3 for the next period.
--
--   **Formalization Note.** The boundedness hypothesis is the standing convention of §X ("all functions appearing in this paper are assumed to be real valued"); without it Lean's infimum would be $0$ on an unbounded set.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), p. 418, Lemma 2

import Mathlib
import Definitions.Def_PorteusSS_Functions
import Definitions.Def_PorteusSS_OrderingCost
import Definitions.Def_PorteusSS_Model

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Lemma 2 (p. 418). If `x ≤ y` and `n ≥ 1`, then `f_n(x) ≤ f_n(y) + c(y - x)`. The hypothesis
`hfin` is the paper's standing convention (§X) that `f_n` is real valued, i.e. that each
infimum in (4) is over a set bounded below. -/
theorem valueFn_le_add_cost (c m φ f0 : ℝ → ℝ) (α c0 K0 cInf KInf : ℝ)
    (hmodel : IsModel c m φ α c0 K0 cInf KInf) (n : ℕ) (hn : 1 ≤ n)
    (hfin : ∀ x : ℝ, BddBelow (range fun w : Ici x => c ((w : ℝ) - x) + hFn c m φ f0 α n w))
    (x y : ℝ) (hxy : x ≤ y) :
    valueFn c m φ f0 α n x ≤ valueFn c m φ f0 α n y + c (y - x) := by sorry

end PorteusSS
