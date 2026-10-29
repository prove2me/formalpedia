-- Prove2me | Theorems.Thm_PochetWolsey_Capacities_initial_stock_hull
-- name    : PochetWolsey.Capacities.initial_stock_hull
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:49.751185+00:00
-- url     : https://prove2.me/theorems/de2bea3c-0adc-4dc3-a2df-c60d81bbe668
-- title:
--   Theorem 9.4 — initial-stock constant-capacity mixing hull
-- statement:
--   Let $n\ge1$, $C>0$, and $0\le d_t\le C$ for each period. Let $X^{\mathrm{DLSI-CC}}$ contain the pairs $(s_0,y)$ with nonnegative real initial stock, binary setups, and $s_0+C\sum_{u=1}^t y_u\ge d_{1t}$ for all $t$. Put $b_t=d_{1t}/C$ and $f_t=b_t-\lfloor b_t\rfloor$. For every nonempty subset $T=\{i_1,\ldots,i_r\}$ ordered by nondecreasing fractional parts, put $f_{i_0}=0$ and
--   $$
--   R_T(y)=C\sum_{\tau=1}^r(f_{i_\tau}-f_{i_{\tau-1}})\left(\lfloor b_{i_\tau}\rfloor+1-\sum_{u=1}^{i_\tau}y_u\right).
--   $$
--   Then
--   $$
--   \operatorname{conv}(X^{\mathrm{DLSI-CC}})=\left\{(s_0,y):\begin{array}{l}
--   s_0\ge0,\quad y\in[0,1]^n,\\
--   s_0+C\sum_{u=1}^t y_u\ge d_{1t}\quad\text{for all }t,\\
--   s_0\ge R_T(y)\quad\text{for all }T,\\
--   s_0\ge R_T(y)+C(1-f_{i_r})(\lfloor b_{i_1}\rfloor-\sum_{u=1}^{i_1}y_u)\quad\text{for all }T
--   \end{array}\right\}.
--   $$
--   This supplies the one-stock constituent hull used in the chapter's decomposition.
--
--   **Formalization Note** Every distinct-period enumeration sorted by fractional part is allowed, including ties and orders that are not chronological. Nonempty subsets are enumerated with `Fin (m+1)`, and the first summand is separated from the remaining finite sum. The empty-subset first cut is already $s_0\ge0$; the second family requires a first and last element. All definitions are expanded locally in the statement for independent auditing.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, DOI 10.1007/0-387-33477-7, p. 280 (PDF 293), Theorem 9.4

import Mathlib
import Definitions.Def_PochetWolsey_Capacities_MixingCuts

namespace PochetWolsey.Capacities

/-- Theorem 9.4. Nonempty subsets are enumerated by injective maps; ordering is by
fractional part, not time. The first summand uses the artificial predecessor value zero. -/
theorem initial_stock_hull {n : ℕ} (hn : 0 < n) (C : ℝ) (hC : 0 < C)
    (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t ∧ d t ≤ C) :
    let b : Fin n → ℝ := fun t => (∑ u ∈ Finset.Iic t, d u) / C
    let f : Fin n → ℝ := fun t => b t - (⌊b t⌋ : ℤ)
    let r := fun (y : Fin n → ℝ) (m : ℕ) (i : Fin (m + 1) → Fin n) =>
      let a : Fin n → ℝ := fun t => (⌊b t⌋ : ℤ) + 1 - ∑ u ∈ Finset.Iic t, y u
      C * (f (i 0) * a (i 0) +
        ∑ j : Fin m, (f (i j.succ) - f (i j.castSucc)) * a (i j.succ))
    convexHull ℝ {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1 ∧
      (∀ u, p.2 u = 0 ∨ p.2 u = 1) ∧
      ∀ t, (∑ u ∈ Finset.Iic t, d u) ≤ p.1 + C * ∑ u ∈ Finset.Iic t, p.2 u} =
    {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1 ∧ (∀ u, 0 ≤ p.2 u ∧ p.2 u ≤ 1) ∧
      (∀ t, (∑ u ∈ Finset.Iic t, d u) ≤ p.1 + C * ∑ u ∈ Finset.Iic t, p.2 u) ∧
      ∀ (m : ℕ) (i : Fin (m + 1) → Fin n), Function.Injective i →
        Monotone (fun j => f (i j)) →
        r p.2 m i ≤ p.1 ∧
        r p.2 m i + C * (1 - f (i (Fin.last m))) *
          ((⌊b (i 0)⌋ : ℤ) - (∑ u ∈ Finset.Iic (i 0), p.2 u)) ≤ p.1} := by sorry

end PochetWolsey.Capacities
