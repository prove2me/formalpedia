-- Prove2me | Theorems.Thm_TrigPolynomial_exists_global_of_local
-- name    : TrigPolynomial.exists_global_of_local
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:59:12.988976+00:00
-- url     : https://prove2.me/theorems/7971cb33-2bf2-45dc-b631-311d96e330af
-- title:
--   A function locally of first harmonic form is globally of that form
-- statement:
--   Let $k\ne0$, $\delta>0$, and let $q:\mathbb R\to\mathbb R$ have the property that for every base point $t_0$ there are coefficients $D(t_0),A(t_0),B(t_0)$ with
--
--   $$
--   q(t)=D(t_0)+A(t_0)\cos(kt)+B(t_0)\sin(kt)\qquad\text{whenever }|t-t_0|<\delta .
--   $$
--
--   Then the coefficients may be taken independent of $t_0$: there are $D,A,B$ with $q(t)=D+A\cos(kt)+B\sin(kt)$ for **all** $t\in\mathbb R$.
--
--   **Role.** This is the passage from a local description with possibly varying data to a single global formula, and the only input beyond the local hypothesis is the connectedness of the line. Two base points closer than $\delta/2$ have overlapping windows, on which the two representations differ by a first harmonic vanishing on an open set, so the coefficient triples agree; the set of base points whose triple equals that of the origin is therefore both open and closed, and nonempty, hence everything.
--
--   It is exactly the step in the analysis of a homogeneous harmonic map into a Euclidean building at which local information becomes global. Near each point of the circle the map takes values in a single apartment, where the squared distance to the cone point is a first harmonic in $2\alpha\theta$; different points of the circle may require different apartments and hence produce different-looking coefficients, and this statement is what shows they must in fact be the same ones.
-- source:
--   Elementary real analysis. The gluing statement is the argument in the proof of Theorem 3.1 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608, that the coefficients of the local representation of the squared distance are independent of the apartment and of the base point, so the local representation is valid on the whole circle. Mathlib has Fourier series and trigonometric polynomials but no uniqueness of coefficients from local data.

import Mathlib

namespace TrigPolynomial

open Filter Topology

theorem exists_global_of_local (k : ℝ) (hk : k ≠ 0) (q : ℝ → ℝ) (delta : ℝ) (hd : 0 < delta)
    (Dc Ac Bc : ℝ → ℝ)
    (hrep : ∀ t0 t : ℝ, |t - t0| < delta →
      q t = Dc t0 + Ac t0 * Real.cos (k * t) + Bc t0 * Real.sin (k * t)) :
    ∃ D A B : ℝ, ∀ t : ℝ, q t = D + A * Real.cos (k * t) + B * Real.sin (k * t) := by sorry

end TrigPolynomial
