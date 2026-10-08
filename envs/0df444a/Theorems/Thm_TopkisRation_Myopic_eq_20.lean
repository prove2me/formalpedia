-- Prove2me | Theorems.Thm_TopkisRation_Myopic_eq_20
-- name    : TopkisRation.Myopic.eq_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:30.957526+00:00
-- url     : https://prove2.me/theorems/60649a8c-c52e-40fc-b059-4d431b3ecca0
-- title:
--   Equation (20), pp. 175–176 — actual and myopic costs agree below the next level
-- statement:
--   For $2\le m\le N$, let $x\ge0$ minimize the actual period-$m$ cost $\widetilde g^{,m}$. Then for a nonnegative stock level $z\le x$, the actual and myopic costs in period $m-1$ differ by the constant $C_m(x)$; for $z\ge x$, the actual cost is at least the myopic cost plus that constant:
--
--   $$\widetilde g^{,m-1}(z)=g^{m-1}(z)+C_m(x)\quad(0\le z\le x),\qquad \widetilde g^{,m-1}(z)\ge g^{m-1}(z)+C_m(x)\quad(z\ge x).$$
--
--   Equation (20) is the comparison that transfers a myopic minimum to an optimal dynamic order-up-to level.
--
--   **Formalization Note** The paper writes $x=\bar y_m$ in the induction, when it has already established that $\bar y_m$ minimizes $\widetilde g^{,m}$.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), pp. 175–176, proof of Theorem 4, equation (20)

import Definitions.Def_TopkisRation_Myopic_MultiPeriod

namespace TopkisRation.Myopic

variable {n : ℕ}

/-- Equation (20), pp. 175–176: comparison of actual and myopic period costs. -/
theorem eq_20 (Q : MultiModel n) (hQ : Q.Standing)
    (m : ℕ) (hm2 : 2 ≤ m) (hmN : m ≤ Q.N)
    (x : ℝ) (hx : 0 ≤ x)
    (hmin : ∀ z, 0 ≤ z → Q.gtilde m x ≤ Q.gtilde m z) :
    (∀ z, 0 ≤ z → z ≤ x →
      Q.gtilde (m - 1) z = Q.gmyopic (m - 1) z + Q.C m x) ∧
    ∀ z, x ≤ z →
      Q.gmyopic (m - 1) z + Q.C m x ≤ Q.gtilde (m - 1) z := by sorry

end TopkisRation.Myopic
