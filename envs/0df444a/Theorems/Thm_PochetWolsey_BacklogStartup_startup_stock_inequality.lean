-- Prove2me | Theorems.Thm_PochetWolsey_BacklogStartup_startup_stock_inequality
-- name    : PochetWolsey.BacklogStartup.startup_stock_inequality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:31:53.761367+00:00
-- url     : https://prove2.me/theorems/df997ef9-4c52-46c1-b21a-658d78a778dc
-- title:
--   Eq. (10.11) — start-up stock inequality
-- statement:
--   Let $d_t\ge0$ be demands and $M\ge d_{1n}$ a sufficiently large production bound. Suppose $s,x\ge0$, the binary setup/start-up plan satisfies (10.5)–(10.8), and $s_{t-1}+x_t=d_t+s_t$, $x_t\le My_t$ in every period. Then for $1\le k\le l\le n$,
--   $$s_{k-1}\ge\sum_{u=k}^l d_u\left(1-y_k-\sum_{j=k+1}^u z_j\right).$$
--   This is the interval stock inequality (10.11), a component of the Wagner–Whitin start-up hull description.
--
--   **Formalization Note** Initial stock is a nonnegative variable, the initial setup state $y_0\in\{0,1\}$ is given, and there is no fixed terminal stock. The bound $M\ge d_{1n}$ explicitly realizes the uncapacitated big-$M$ convention; the inequality does not rely on a special demand instance.
--
--   Initial-state convention: the parameter `y0` is the same fixed binary datum in every feasible set in this item (printed p. 138 / PDF 155); it is not optimized.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 321 (PDF 334), Eq. (10.11)

import Mathlib
import Definitions.Def_PochetWolsey_BacklogStartup_StartupModel

namespace PochetWolsey.BacklogStartup

theorem startup_stock_inequality {n : ℕ} (y0 : ℝ) (hy0 : y0 = 0 ∨ y0 = 1) (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t)
    (M : ℝ) (hM : demandSum d 1 n ≤ M) (p : StartupPoint n) (x : Fin n → ℝ)
    (hp : LSStartup y0 d M p x) (k l : ℕ) (hk : 1 ≤ k) (hkl : k ≤ l) (hl : l ≤ n) :
    startupStockRHS d p k l ≤ stock p.1 (k - 1) := by sorry

end PochetWolsey.BacklogStartup
