-- Prove2me | Theorems.Thm_TopkisRation_Myopic_C_flat_below
-- name    : TopkisRation.Myopic.C_flat_below
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:14.269367+00:00
-- url     : https://prove2.me/theorems/8c34000a-6b41-4155-b644-760fe1ed9381
-- title:
--   Theorem 4 proof, p. 175 — Cₘ is flat below an order-up-to level
-- statement:
--   Let $x\ge0$ be a minimizer of the actual period-$m$ cost $\widetilde g^{,m}$ on $[0,\infty)$. Then the continuation cost is constant for net stock at or below $x$ and cannot fall below that value above $x$:
--
--   $$C_m(w)=C_m(x)\quad(w\le x),\qquad C_m(w)\ge C_m(x)\quad(w\ge x).$$
--
--   The paper applies this observation with $x=\bar y_m$ during the induction for Theorem 4.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 175, proof of Theorem 4, displays before (20)

import Definitions.Def_TopkisRation_Myopic_MultiPeriod

namespace TopkisRation.Myopic

variable {n : ℕ}

/-- Theorem 4 proof, p. 175: `Cₘ` is flat below an optimal order-up-to level. -/
theorem C_flat_below (Q : MultiModel n) (hQ : Q.Standing)
    (m : ℕ) (hm : m ∈ Finset.Icc 1 Q.N)
    (x : ℝ) (hx : 0 ≤ x)
    (hmin : ∀ z, 0 ≤ z → Q.gtilde m x ≤ Q.gtilde m z) :
    (∀ w, w ≤ x → Q.C m w = Q.C m x) ∧
    ∀ w, x ≤ w → Q.C m x ≤ Q.C m w := by sorry

end TopkisRation.Myopic
