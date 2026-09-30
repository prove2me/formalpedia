-- Prove2me | Theorems.Thm_RevenueManagement_joint_overbooking_concave_submodular
-- name    : RevenueManagement.joint_overbooking_concave_submodular
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:42:13.348917+00:00
-- url     : https://prove2.me/theorems/1ef00ab2-e471-4a5c-b774-91b0d1055903
-- title:
--   Proposition 4.4: with Poisson show demands, the expected net revenue G(x) of (4.21) is component-wise concave and submodular in the overbooking levels x
-- statement:
--   In the substitutable-capacity model with nonnegative capacities $C_i$ and show demands
--   $Z_j(x_j) \sim \mathrm{Poisson}(q_j x_j)$ independent across classes, $q_j \ge 0$, the
--   expected net revenue $G$ of (4.21) has decreasing first differences in every direction: for
--   all levels $x$ and all classes $i, j$,
--   $G(x + e_i + e_j) - G(x + e_i) \le G(x + e_j) - G(x)$. With $i = j$ this is
--   component-wise concavity in $x_j$, and with $i \ne j$ submodularity in $x$.
--
--   **Formalization Note** The book prints $G(x) = p^\top(x-y) - \mathbb E[s^\top(x - Z(x))]
--   - \mathbb E[V(Z(x), C)]$ while defining $V$ as the maximum net benefit of the service
--   period; the expected net revenue adds that benefit, and with the printed sign the
--   proposition is false, so the definition uses $+\mathbb E[V(Z(x), C)]$.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 164, Proposition 4.4 ('the function G(x) defined by (4.21) is component-wise concave in each xj and submodular in x. That is, letting ej denote the jth unit vector, for all j, the first differences G(x + ej) − G(x) are decreasing')

import Definitions.Def_RevenueManagement_overbooking

namespace RevenueManagement

theorem joint_overbooking_concave_submodular {n m : ℕ} (h : Fin n → Fin (m + 1) → ℝ)
    (Cap : Fin (m + 1) → ℝ) (hCap : ∀ i, 0 ≤ Cap i) (p s q : Fin n → ℝ) (hq : ∀ j, 0 ≤ q j)
    (y x : Fin n → ℕ) (i j : Fin n) :
    expNetRevenue h Cap p s q y (x + Pi.single i 1 + Pi.single j 1) -
        expNetRevenue h Cap p s q y (x + Pi.single i 1) ≤
      expNetRevenue h Cap p s q y (x + Pi.single j 1) - expNetRevenue h Cap p s q y x := by sorry

end RevenueManagement
