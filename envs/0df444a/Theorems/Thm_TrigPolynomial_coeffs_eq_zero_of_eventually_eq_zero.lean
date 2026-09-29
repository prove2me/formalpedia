-- Prove2me | Theorems.Thm_TrigPolynomial_coeffs_eq_zero_of_eventually_eq_zero
-- name    : TrigPolynomial.coeffs_eq_zero_of_eventually_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:59:11.398686+00:00
-- url     : https://prove2.me/theorems/b7772b0c-31ae-4dcb-bf85-e60ebbda25a3
-- title:
--   A first harmonic vanishing near a point has vanishing coefficients
-- statement:
--   Let $k\ne0$ and suppose that
--
--   $$
--   D+A\cos(kx)+B\sin(kx)=0
--   $$
--
--   for every $x$ in some neighbourhood of a point $x_0$. Then $D=A=B=0$.
--
--   **Role.** The three functions $1$, $\cos(kx)$, $\sin(kx)$ are linearly independent, but the usual proof of that — orthogonality over a full period — needs the identity on an interval of length $2\pi/|k|$. This statement is the sharper local form: vanishing on an arbitrarily short interval already forces the coefficients to vanish, so the representation of a function as a first harmonic is unique as soon as it is known anywhere.
--
--   That is what licenses gluing. If a function is known to agree with *some* first harmonic near each point, the coefficients cannot vary: two overlapping representations differ by a first harmonic vanishing on the overlap, hence agree. Over a connected parameter space the local coefficients are therefore globally constant, and a purely local description becomes a global formula.
--
--   The proof is a differentiation rather than an integration: on the neighbourhood the function and its first two derivatives vanish, and the second derivative kills the constant $D$, leaving the pair of equations $A\cos(kx_0)+B\sin(kx_0)=0$ and $-A\sin(kx_0)+B\cos(kx_0)=0$, whose matrix is a rotation and hence invertible.
-- source:
--   Elementary real analysis. The gluing statement is the argument in the proof of Theorem 3.1 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608, that the coefficients of the local representation of the squared distance are independent of the apartment and of the base point, so the local representation is valid on the whole circle. Mathlib has Fourier series and trigonometric polynomials but no uniqueness of coefficients from local data.

import Mathlib

namespace TrigPolynomial

open Filter Topology

theorem coeffs_eq_zero_of_eventually_eq_zero (k : ℝ) (hk : k ≠ 0) (D A B x0 : ℝ)
    (h : ∀ᶠ x in 𝓝 x0, D + A * Real.cos (k * x) + B * Real.sin (k * x) = 0) :
    D = 0 ∧ A = 0 ∧ B = 0 := by sorry

end TrigPolynomial
