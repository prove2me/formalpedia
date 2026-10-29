-- Prove2me | Theorems.Thm_PochetWolsey_BacklogStartup_ww_startup_hull
-- name    : PochetWolsey.BacklogStartup.ww_startup_hull
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:31:53.185725+00:00
-- url     : https://prove2.me/theorems/751780e3-da33-4fc3-9c76-c05b8183aa67
-- title:
--   Theorem 10.15 — printed Wagner–Whitin start-up hull
-- statement:
--   Let $n\ge1$ and $d_t\ge0$. Let $X^{WW-U-SC}$ be the set defined by (10.14)–(10.17), with given $y_0\in\{0,1\}$. The printed theorem asserts
--   $$\operatorname{conv}(X^{WW-U-SC})=P_{\rm printed},$$
--   where $P_{\rm printed}$ is the system (10.11), (10.15), (10.16), $s\ge0$, and $0\le y\le1$. This asserts equality of the entire sets in $(s,y,z)$ space, including the free nonnegative terminal-stock direction.
--
--   The item preserves the printed hull assertion as the source milestone. Finding F1 supplies a counterexample to its missing lower bound on start-ups, so this faithful item is expected to be disproved.
--
--   **Formalization Note** The right-hand side deliberately does not impose $z\ge0$. The corrected variant is separate; it does not replace this statement or its milestone.
--
--   Initial-state convention: the parameter `y0` is the same fixed binary datum in every feasible set in this item (printed p. 138 / PDF 155); it is not optimized.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 323 (PDF 336), Theorem 10.15

import Mathlib
import Definitions.Def_PochetWolsey_BacklogStartup_StartupModel

namespace PochetWolsey.BacklogStartup

theorem ww_startup_hull {n : ℕ} (y0 : ℝ) (hy0 : y0 = 0 ∨ y0 = 1) (hn : 0 < n) (d : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t) :
    convexHull ℝ (WWStartup y0 d) = PrintedStartupHull y0 d := by sorry

end PochetWolsey.BacklogStartup
