-- Prove2me | Theorems.Thm_Transcendence_circle_vanishing_ideal
-- name    : Transcendence.circle_vanishing_ideal
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:15:52.953711+00:00
-- url     : https://prove2.me/theorems/34aa451a-2be0-45d2-a15a-2e448571c4ed
-- title:
--   The polynomials vanishing at a point of a circle with a transcendental coordinate
-- statement:
--   Let $K$ be a subfield of $\mathbb{C}$ and $\rho \in K$ non-zero. Let $(x, y) \in \mathbb{C}^{2}$ lie on the circle $x^{2} + y^{2} = \rho$, with $y$ transcendental over $K$. Then for every $P \in K[X_0, X_1]$,
--
--   $$P(x, y) = 0 \iff X_0^{2} + X_1^{2} - \rho \ \text{divides}\ P.$$
--
--   So every plane curve defined over $K$ that passes through $(x, y)$ contains the whole circle.
-- source:
--   Standard. Formal proof: Diaz modulus mission, 25 September 2026 (C. Perassi); extracted from the proof of DiazModulus.candidate_vanishing_ideal, which is the case K = Q̄, (x, y) = (Re u, Im u).

import Mathlib

namespace Transcendence

theorem circle_vanishing_ideal {K : Subfield ℂ} {x y : ℂ} {ρ : K} (hρ : ρ ≠ 0)
    (hxy : x ^ 2 + y ^ 2 = (ρ : ℂ)) (hy : Transcendental K y) (P : MvPolynomial (Fin 2) K) :
    MvPolynomial.aeval ![x, y] P = 0 ↔
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - MvPolynomial.C ρ) ∣ P := by
  sorry

end Transcendence
