-- Prove2me | Theorems.Thm_StallEconomy_Magnet_rule_valid
-- name    : StallEconomy.Magnet.rule_valid
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:39.572879+00:00
-- url     : https://prove2.me/theorems/9f072a40-2095-4c7e-b6be-19378e3b5335
-- title:
--   §3.3, p. 16 — the magnet rule stays in the inner diamond and preserves the walking radius
-- statement:
--   Fix integers $k,h\ge0$ with $2h\le k$. If the stall starts at $z_o\in\mathcal I_0$ and the customer is at $z_c\in G_k$, the magnet-rule rendezvous $z_d=m_{k,h}(z_o,z_c)$ remains in $\mathcal I_0$. If $z_c\notin\mathcal I(z_o)$, the customer travels exactly $h$ grid units:
--   $$
--   z_d\in\mathcal I_0,\qquad
--   \max\{|x_c-x_d|,|y_c-y_d|\}=h.
--   $$
--
--   In the paper's edge coordinates the Manhattan distance is $\sqrt2R/k$ times this maximum, so the second equality is the customer's walking distance $r$ when $k>0$.
--
--   **Formalization Note** The theorem includes $k=0,h=0$: the only grid point is the stall and customer location, and the outside-small-diamond clause is empty.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), pp. 13, 16, §3.3 paragraph after Definition 2; p. 45, grid distance

import Mathlib
import Definitions.Def_StallEconomy_Magnet_Setting

namespace StallEconomy.Magnet

theorem rule_valid (k h : ℕ) (hkh : 2 * h ≤ k)
    (zo zc : ℤ × ℤ) (hzo : zo ∈ inner k h) (hzc : zc ∈ grid k) :
    magnet k h zo zc ∈ inner k h ∧
      (zc ∉ smallDiamond h zo →
        max |zc.1 - (magnet k h zo zc).1|
          |zc.2 - (magnet k h zo zc).2| = (h : ℤ)) := by sorry

end StallEconomy.Magnet
