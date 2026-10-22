-- Prove2me | Theorems.Thm_WalledBrauer_Center_proposition_2_7
-- name    : WalledBrauer.Center.proposition_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:31.416381+00:00
-- url     : https://prove2.me/theorems/9506385a-2d53-4665-b980-1f7e3303320a
-- title:
--   Proposition 2.7 — $L_1^k+\dots+L_r^k+(-1)^{k+1}(L_{r+1}^k+\dots+L_{r+s}^k)$ is central
-- statement:
--   For every integer $k\ge0$, the element
--
--   $$
--   L_1^k+\dots+L_r^k+(-1)^{k+1}\bigl(L_{r+1}^k+\dots+L_{r+s}^k\bigr)
--   $$
--
--   of the walled Brauer algebra $B_{r,s}(\delta)$ lies in the center $Z(B_{r,s}(\delta))$. This element is the power sum supersymmetric polynomial $p_k$ evaluated at the Jucys–Murphy elements. Together with Stembridge's theorem it shows that every supersymmetric polynomial in $L_1,\dots,L_{r+s}$ is central (Corollary 2.9).
--
--   **Formalization Note** The element is `jmPowerSum δ k`, the sums running over 0-based vertices $i<r$ and $r\le i$. The center is `Subalgebra.center ℂ`, which is the same set for the platform's product and its opposite.
-- source:
--   Jung–Kim, Supersymmetric polynomials and the center of the walled Brauer algebra, arXiv:1508.06469v2, p. 10, Proposition 2.7

import Mathlib
import Definitions.Def_WalledBrauer_Center_Setting

namespace WalledBrauer.Center
open WalledBrauer.Blocks MvPolynomial

theorem proposition_2_7 (r s : ℕ) (δ : ℂ) (k : ℕ) :
    jmPowerSum (r := r) (s := s) δ k ∈ Subalgebra.center ℂ (B r s δ) := by sorry
end WalledBrauer.Center
