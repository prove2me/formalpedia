-- Prove2me | Theorems.Thm_VRPTWColGen92_Bound_restricted_optimal_is_optimal
-- name    : VRPTWColGen92.Bound.restricted_optimal_is_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:37:42.727386+00:00
-- url     : https://prove2.me/theorems/e9231f87-91ce-4904-81ea-12cb465010f0
-- title:
--   Secs. 4–5, pp. 346 and 348 — if no 2-cycle-free column has negative marginal cost, the restricted LP optimum is optimal for the full LP relaxation
-- statement:
--   This is the stopping test of the column generation procedure, stated with column marginal costs.
--
--   Let $R_0$ be a finite set of 2-cycle-free paths (the current columns). Let $\bar z = (\bar x, \bar X_d, \bar X_c)$ be an optimal solution of the LP relaxation of the set covering type model (1)–(6) restricted to the columns $R_0$, and let $(\pi, \pi_d, \pi_c)$ be an optimal solution of the dual of that restricted LP. Suppose that every 2-cycle-free path $r$ of the instance has nonnegative marginal cost:
--   $$\bar c_r = c_r - \sum_{i\in N\setminus\{d\}}\pi_i\gamma_{ir} - \pi_d - \pi_c c_r \ \ge\ 0.$$
--   Then $\bar z$ is an optimal solution of the LP relaxation of (1)–(6) over the set of **all** 2-cycle-free paths.
--
--   The pricing hypothesis ranges over every 2-cycle-free path, not only over the current columns; it is what the subproblem certifies when it finds no negative marginal cost column.
--
--   **Formalization Note.** No condition on the instance data is needed. The LP relaxation keeps $X_d, X_c \ge 0$ and relaxes $x_r \in\{0,1\}$ to $x_r \ge 0$; the dual is that of the restricted LP, with $\pi_i, \pi_d, \pi_c \ge 0$.
-- source:
--   Desrochers, Desrosiers & Solomon, A new optimization algorithm for the vehicle routing problem with time windows, Oper. Res. 40 (1992), p. 346, Sec. 4, and p. 348, Sec. 5

import Mathlib
import Definitions.Def_VRPTWColGen92_Bound_Network
import Definitions.Def_VRPTWColGen92_Bound_CoveringLP

namespace VRPTWColGen92.Bound
theorem restricted_optimal_is_optimal {n : ℕ} (I : Instance n)
    (R₀ : Finset (List (Fin (n + 1)))) (hR₀ : ∀ p ∈ R₀, IsPath3 I p)
    (z : LPPoint n) (hz : LPOptimal I (↑R₀ : Set (List (Fin (n + 1)))) z)
    (y : DualPoint n) (hy : DualOptimal I R₀ y)
    (hprice : ∀ p, IsPath3 I p → 0 ≤ columnMarginal I y p) :
    LPOptimal I {p | IsPath3 I p} z := by sorry
end VRPTWColGen92.Bound
