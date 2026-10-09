-- Prove2me | Theorems.Thm_SphereSOS_Rate_gegenbauer_deriv_one
-- name    : SphereSOS.Rate.gegenbauer_deriv_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:19:13.717114+00:00
-- url     : https://prove2.me/theorems/e88ad61b-bf64-4fcc-a279-54d07acc3da9
-- title:
--   Proof of Prop. 18, p. 16 — $C_i'(1)/C_i(1)=i(i+d-2)/(d-1)$
-- statement:
--   Let $d\ge2$ and let $C_i$ be the Gegenbauer polynomial of degree $i$ for $S^{d-1}$. Then
--   $$\frac{C_i'(1)}{C_i(1)}=\frac{i\,(i+d-2)}{d-1}.$$
--
--   This value feeds the tangent-line bound of Proposition 18 and the computation of $h'(1)$ in the proof of Proposition 7.
--
--   **Formalization Note** Stated for the normalized polynomial $P_i=C_i/C_i(1)$, for which $P_i'(1)=C_i'(1)/C_i(1)$.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 16, proof of Proposition 18, last paragraph

import Mathlib
import Definitions.Def_SphereSOS_Rate_Gegenbauer

namespace SphereSOS.Rate

theorem gegenbauer_deriv_one (d i : ℕ) (hd : 2 ≤ d) :
    (geg d i).derivative.eval 1 = (i : ℝ) * ((i : ℝ) + (d : ℝ) - 2) / ((d : ℝ) - 1) := by sorry

end SphereSOS.Rate
