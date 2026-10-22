-- Prove2me | Theorems.Thm_UhlmannRoof_RankTwo_eq_13
-- name    : UhlmannRoof.RankTwo.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:39.332469+00:00
-- url     : https://prove2.me/theorems/60ffe019-7232-4e37-8051-13f5d252656f
-- title:
--   Equation (13), p. 9 — the rank two support projection
-- statement:
--   Let $D$ be the density operator of a rank two state and $Q$ its support, the orthogonal projection onto the range of $D$. Then
--   $$\frac12 Q=(1-\operatorname{Tr}D^2)^{-1}(D-D^2).$$
--   This identifies the support projection from a quadratic expression in $D$.
--
--   **Formalization Note** Orthogonal projection is expressed by $Q^2=Q$ and $Q^*=Q$; equality of ranges identifies it as the support. Rank two and the trace one positive semidefinite condition ensure the denominator is nonzero.
-- source:
--   Uhlmann, arXiv:quant-ph/9704017v2, p. 9, eq. (13)

import Mathlib
import Definitions.Def_UhlmannRoof_RankTwo_Model

namespace UhlmannRoof.RankTwo

/-- Uhlmann, equation (13), p. 9: the rank-two support projection
is a normalized quadratic expression in the density operator. -/
theorem eq_13 {d : ℕ} (D : Mat d) (hD : IsState D) (hrk : D.rank = 2)
    (Q : Mat d) (hQid : Q * Q = Q)
    (hQsa : Matrix.conjTranspose Q = Q)
    (hQrange : LinearMap.range (Matrix.toLin' Q) =
      LinearMap.range (Matrix.toLin' D)) :
    (1 / 2 : ℂ) • Q = ((1 - (D * D).trace)⁻¹) • (D - D * D) := by sorry

end UhlmannRoof.RankTwo
