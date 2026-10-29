-- Prove2me | Theorems.Thm_PochetWolsey_WagnerWhitin_ww_inequality_rewriting
-- name    : PochetWolsey.WagnerWhitin.ww_inequality_rewriting
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:51.92579+00:00
-- url     : https://prove2.me/theorems/c46dc878-ec59-4d00-850e-cf794cbb7685
-- title:
--   Observation 7.12 — equivalent Wagner–Whitin inequalities
-- statement:
--   Let $n\ge1$, $d_t\ge0$, and real vectors $x,y,s$ satisfy $s_0=0$ and $s_{t-1}+x_t=d_t+s_t$. For $1\le k\le l\le n$, the following three inequalities are equivalent:
--   $$s_{k-1}\ge\sum_{j=k}^l d_j\Bigl(1-\sum_{u=k}^j y_u\Bigr),$$
--   $$s_{k-1}+\sum_{j=k}^l d_{jl}y_j\ge d_{kl},$$
--   $$\sum_{j=1}^{k-1}x_j+\sum_{j=k}^l d_{jl}y_j\ge d_{1l}.$$
--   Here $d_{ab}=\sum_{j=a}^b d_j$. The observation relates the stock formulation to an $(l,S)$ inequality.
--
--   **Formalization Note** The last expression uses the chapter's default $s_0=0$ and balance equations. These assumptions do not constrain the separate goal's initial stock. No setup integrality or sign condition on $x,y,s$ is needed for these algebraic rewritings.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 225 (PDF 239), Observation 7.12

import Mathlib

open scoped BigOperators

namespace PochetWolsey.WagnerWhitin

theorem ww_inequality_rewriting (n : ℕ) (hn : 0 < n)
    (d x y : Fin n → ℝ) (s : Fin (n + 1) → ℝ)
    (hd : ∀ t, 0 ≤ d t) (hs0 : s 0 = 0)
    (hbalance : ∀ t, s t.castSucc + x t = d t + s t.succ)
    (k l : Fin n) (hkl : k ≤ l) :
    (s k.castSucc ≥ ∑ j ∈ Finset.Icc k l,
      d j * (1 - ∑ u ∈ Finset.Icc k j, y u) ↔
      s k.castSucc + ∑ j ∈ Finset.Icc k l,
        (∑ u ∈ Finset.Icc j l, d u) * y j ≥ ∑ j ∈ Finset.Icc k l, d j) ∧
    (s k.castSucc + ∑ j ∈ Finset.Icc k l,
        (∑ u ∈ Finset.Icc j l, d u) * y j ≥ ∑ j ∈ Finset.Icc k l, d j ↔
      (∑ j ∈ Finset.Iio k, x j) + ∑ j ∈ Finset.Icc k l,
        (∑ u ∈ Finset.Icc j l, d u) * y j ≥ ∑ j ∈ Finset.Iic l, d j) := by sorry

end PochetWolsey.WagnerWhitin
