-- Prove2me | Theorems.Thm_SphereSOS_Rate_hpoly_deriv_one
-- name    : SphereSOS.Rate.hpoly_deriv_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:19:28.479989+00:00
-- url     : https://prove2.me/theorems/58751bf7-848a-4c81-801c-0647ef2e0a88
-- title:
--   Proof of Prop. 7, p. 9 — $h'(1)=(n+1)(3d+4n-4)/(3(d-1))$
-- statement:
--   Let $d\ge2$, $n\ge1$, and $h=\frac1n\sum_{k=1}^nC_{2k}/C_{2k}(1)$. Then
--   $$h'(1)=\frac{(n+1)(3d+4n-4)}{3(d-1)}.$$
--
--   This is the slope of the tangent line that bounds $h$ from below, and so controls how far $\lambda_{\max}(\mathcal T[h])$ can fall below $1$.
--
--   **Formalization Note** A direct consequence of $C_i'(1)/C_i(1)=i(i+d-2)/(d-1)$; it is quoted from the page as the exact value it gives.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 9, proof of Proposition 7, final sentence

import Mathlib
import Definitions.Def_SphereSOS_Rate_Toeplitz

namespace SphereSOS.Rate

theorem hpoly_deriv_one (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n) :
    (hpoly d n).derivative.eval 1 =
      ((n : ℝ) + 1) * (3 * (d : ℝ) + 4 * (n : ℝ) - 4) / (3 * ((d : ℝ) - 1)) := by sorry

end SphereSOS.Rate
