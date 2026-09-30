-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_frontier_contact_order
-- name    : WeierstrassEllipticZeta.frontier_contact_order
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-12T20:59:22.513182+00:00
-- url     : https://prove2.me/theorems/8ef05c80-0fc9-4ecf-86b4-4a81d69cb9cc
-- title:
--   Contact ideals and analytic vanishing order
-- statement:
--   Fix the elliptic-extension geometry with its compatible jet and contact-ideal identities. Let $c$ be a chart, let $p$ be any polynomial in its four affine coordinates, and let $z$ be a point with nonzero chart denominator. For every integer $k\ge0$, write $f(w)=p(\operatorname{coords}_c(w))$. Then
--   $$p\in I_c(z,k)\iff k\le\operatorname{ord}_z(f),\qquad p\notin I_c(z,k)\iff\operatorname{ord}_z(f)<k.$$
--   The order takes values in the extended natural numbers, so the equivalences include the identically vanishing germ and $k=0$. This converts the algebraic contact condition into the analytic hypothesis used by the multiplicity estimate.
-- source:
--   Derived equivalence in the differential-ideal approach of Senthil Kumar K (2026), Appendix A and A.2, https://doi.org/10.1017/S001309152610145X. Uses the previously established chart jet-order and contact-ideal membership identities, now projected from the geometry interface.

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.frontier_contact_order
    (G : Frontier.Geometry) (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ)
    (z : ℂ) (hz : G.S (extensionChartDenominator c) z ≠ 0) (k : ℕ) :
    (p ∈ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
        (extensionChartCoordinates G.S c z) k ↔
      (k : ℕ∞) ≤ analyticOrderAt
        (fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w) p) z) ∧
    (p ∉ extensionChartContactIdeal G.L.g₂ G.L.g₃ c
        (extensionChartCoordinates G.S c z) k ↔
      analyticOrderAt
        (fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w) p) z < k) := by sorry
