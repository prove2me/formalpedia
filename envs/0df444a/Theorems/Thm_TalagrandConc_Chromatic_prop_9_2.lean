-- Prove2me | Theorems.Thm_TalagrandConc_Chromatic_prop_9_2
-- name    : TalagrandConc.Chromatic.prop_9_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:46.319852+00:00
-- url     : https://prove2.me/theorems/d7364647-5670-45f4-b9e5-c5ca5c4e3252
-- title:
--   Proposition 9.2 — $P(G(n,p)\text{ has no independent }r\text{-set})\le2\exp(-u^2/(r^2(r-1)^2))$
-- statement:
--   Let $G(n,p)$, $0<p<1$, be the random graph on $V=\{1,\dots,n\}$, fix an integer $r\ge2$, and for $e=(i,j)\in E_0$ let $N(G,e)$ be the number of independent sets of size $r$ of $G$ containing $i$ and $j$. Let $u\ge0$ and assume
--   $$P\Big(G(n,p)\text{ contains an independent set of size }r\ \text{ and }\ u\sqrt{\textstyle\sum_{e\in E_0}N(G(n,p),e)^2}\le\sum_{e\in E_0}N(G(n,p),e)\Big)>\frac12.$$
--   Then
--   $$P\big(G(n,p)\text{ contains no independent set of size }r\big)\le2\exp\Big(-\frac{u^2}{r^2(r-1)^2}\Big).$$
--
--   This is a Janson-type upper bound on the probability that $G(n,p)$ has independence number below $r$, obtained directly from the convex-hull inequality; it is the input for the greedy upper bound on the chromatic number.
--
--   **Formalization Note** On the page, hypothesis (9.4) reads $P\big(u\sqrt{\sum_e N^2}\le\sum_e N\big)>\frac12$. Read literally this is false: when $G(n,p)$ has no independent $r$-set (e.g. $r>n$, or $p$ close to $1$) both sums vanish, so (9.4) holds for every $u$ while the left side of the conclusion is close to $1$. The proof uses a point of the (9.4) event that lies outside the set $A$ of graphs with no independent $r$-set (it divides by $N>0$), so the event is intersected here with \"$G(n,p)$ contains an independent set of size $r$\", i.e. $\sum_e N(G,e)>0$. The page's \"a number $u$\" is taken nonnegative (for $u<0$ the conclusion fails), and $r\ge2$ makes $r(r-1)\ne0$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 164, Proposition 9.2, Eq. (9.4) (N(G,e) defined on p. 164; proof pp. 164–165)

import Mathlib
import Definitions.Def_TalagrandConc_Chromatic_Basic

open MeasureTheory
open scoped Classical

namespace TalagrandConc.Chromatic

theorem prop_9_2 (n r : ℕ) (p u : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hr : 2 ≤ r) (hu : 0 ≤ u)
    (h94 : (1 / 2 : ℝ) < (gnp n p).real
      {x | 0 < ∑ e : EdgeSlot n, (indepCount (graphOf x) r e : ℝ) ∧
        u * Real.sqrt (∑ e : EdgeSlot n, (indepCount (graphOf x) r e : ℝ) ^ 2)
          ≤ ∑ e : EdgeSlot n, (indepCount (graphOf x) r e : ℝ)}) :
    (gnp n p).real {x | ∀ s : Finset (Fin n), ¬ (graphOf x).IsNIndepSet r s}
      ≤ 2 * Real.exp (-(u ^ 2 / ((r : ℝ) ^ 2 * ((r : ℝ) - 1) ^ 2))) := by sorry

end TalagrandConc.Chromatic
