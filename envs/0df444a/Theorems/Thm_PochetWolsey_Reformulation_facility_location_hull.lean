-- Prove2me | Theorems.Thm_PochetWolsey_Reformulation_facility_location_hull
-- name    : PochetWolsey.Reformulation.facility_location_hull
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:47.862723+00:00
-- url     : https://prove2.me/theorems/28ebc150-0827-4bd7-a621-0e8786aa072d
-- title:
--   Theorem 4.1 — multi-commodity relaxation gives the lot-sizing hull
-- statement:
--   Let $n\ge1$ be the horizon, let $d_t\ge0$ be demands, and let the fixed initial stock be $a$ with $0\le a\le d_1$. Final stock is zero. The original lot-sizing set $X$ has nonnegative production and inventory, binary setups, the balances $s_{i-1}+x_i=d_i+s_i$, and $x_i\le d_{in}y_i$, where $d_{in}=\sum_{t=i}^n d_t$.
--
--   In the multi-commodity relaxation $Q$, $w_{it}\ge0$ is production in period $i$ for demand period $t$, and $v_{it}\ge0$ is its inventory after period $i$. The only production variables have $i\le t$; stocks end at $v_{tt}=0$. Set $v_{01}=a$, $v_{0t}=0$ for $t>1$, $\widehat d_1=d_1-a$, and $\widehat d_t=d_t$ for $t>1$. The remaining constraints are
--   $$v_{i-1,t}+w_{it}=\delta_{it}d_t+v_{it},\quad w_{it}\le\widehat d_ty_i,\quad 0\le y_i\le1\qquad(1\le i\le t\le n).$$
--   Here $\delta_{it}$ is one when $i=t$ and zero otherwise. Let $\pi$ sum commodities to recover production and stocks, keeping $y$ unchanged. Then
--   $$\pi(Q)=\operatorname{conv}(X).$$
--   For every real unit production cost $p$, holding cost $h$, and fixed setup cost $q$, the relaxation has an attained optimum with every $y_i\in\{0,1\}$ for the objective
--   $$\sum_{i=1}^n(px_i+qy_i)+\sum_{i=1}^{n-1}hs_i.$$
--   The projected optimum is feasible and optimal for the original lot-sizing problem. Thus both the geometric hull claim and the integral optimal-solution claim are required.
--
--   **Formalization Note** The complete constraints are local let-bindings inside the theorem so the independent reader needs no unseen imported model. Rectangular arrays extend the triangular variables by zeros; the terminal stock is included in the cost sum but is constrained to zero. Production periods use zero-based `Fin n`, whereas boundary stocks use `Fin (n+1)`. The positive-initial-stock case on pp. 119–120 is retained, and setting $a=0$ recovers the normalized case. No demand divisions or optimal-value infima are used.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 121 (PDF 138), Theorem 4.1; Eqs. (4.1)–(4.11), pp. 117–120 (PDF 134–137); DOI 10.1007/0-387-33477-7

import Mathlib

namespace PochetWolsey.Reformulation

theorem facility_location_hull
    (n : ℕ) (hn : 0 < n) (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t)
    (a : ℝ) (ha : 0 ≤ a) (ha_first : ∀ t : Fin n, t.val = 0 → a ≤ d t)
    (p h q : ℝ) :
    let X : Set ((Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
      {z | z.2.1 0 = a ∧ z.2.1 (Fin.last n) = 0 ∧
        (∀ k, 0 ≤ z.2.1 k) ∧
        (∀ i, 0 ≤ z.1 i ∧ (z.2.2 i = 0 ∨ z.2.2 i = 1) ∧
          z.2.1 i.castSucc + z.1 i = d i + z.2.1 i.succ ∧
          z.1 i ≤ (∑ t ∈ Finset.univ.filter (fun t => i ≤ t), d t) * z.2.2 i)}
    let Q := fun (w : Fin n → Fin n → ℝ) (v : Fin (n + 1) → Fin n → ℝ)
        (y : Fin n → ℝ) =>
      (∀ i t, 0 ≤ w i t) ∧ (∀ k t, 0 ≤ v k t) ∧
      (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧
      (∀ i t, t < i → w i t = 0) ∧
      (∀ k t, t.val < k.val → v k t = 0) ∧
      (∀ t, v 0 t = if t.val = 0 then a else 0) ∧
      (∀ i t, i ≤ t →
        v i.castSucc t + w i t = (if i = t then d t else 0) + v i.succ t) ∧
      (∀ i t, i ≤ t → w i t ≤ (d t - (if t.val = 0 then a else 0)) * y i)
    let project := fun (w : Fin n → Fin n → ℝ) (v : Fin (n + 1) → Fin n → ℝ)
        (y : Fin n → ℝ) => ((fun i => ∑ t, w i t), (fun k => ∑ t, v k t), y)
    let cost := fun z : (Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      (∑ i, (p * z.1 i + q * z.2.2 i)) + (∑ i : Fin n, h * z.2.1 i.succ)
    {z | ∃ w v y, Q w v y ∧ z = project w v y} = convexHull ℝ X ∧
      ∃ w v y, Q w v y ∧ (∀ i, y i = 0 ∨ y i = 1) ∧
        (∀ w' v' y', Q w' v' y' → cost (project w v y) ≤ cost (project w' v' y')) ∧
        project w v y ∈ X ∧ (∀ z ∈ X, cost (project w v y) ≤ cost z) := by sorry

end PochetWolsey.Reformulation
