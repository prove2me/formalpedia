-- Prove2me | Theorems.Thm_SphereSOS_Rate_proposition_18
-- name    : SphereSOS.Rate.proposition_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:32.538621+00:00
-- url     : https://prove2.me/theorems/6c3672d9-00f7-4c4f-9bf7-e9be770d04f3
-- title:
--   Proposition 18, p. 16 — $C_i(t)\ge C_i'(1)(t-1)+C_i(1)$ on $[-1,1]$
-- statement:
--   Let $d\ge2$ and let $C_i$ be the Gegenbauer polynomial of degree $i$ for $S^{d-1}$. Then the graph of $C_i$ lies above its tangent at $t=1$ on $[-1,1]$:
--   $$C_i(t)\ge C_i'(1)(t-1)+C_i(1)\qquad\text{for all }t\in[-1,1].$$
--
--   Summed over $i=2k$, it gives $h(t)\ge h'(1)(t-1)+h(1)$ for $h=\frac1n\sum_kC_{2k}/C_{2k}(1)$, which reduces $\mathcal T[h]$ to a Toeplitz matrix of a linear function.
--
--   **Formalization Note** Stated for $P_i=C_i/C_i(1)$; the inequality is invariant under multiplication by $C_i(1)>0$. It holds for every $i\ge0$ (with equality for $i\le1$), even though the printed proof's step $l(0)\le-C_i(1)$ needs $i\ge2$.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 16, Proposition 18

import Mathlib
import Definitions.Def_SphereSOS_Rate_Gegenbauer

namespace SphereSOS.Rate

theorem proposition_18 (d i : ℕ) (hd : 2 ≤ d) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      (geg d i).derivative.eval 1 * (t - 1) + (geg d i).eval 1 ≤ (geg d i).eval t := by sorry

end SphereSOS.Rate
