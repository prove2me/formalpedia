-- Prove2me | Theorems.Thm_TranscendenceTheory_small_values_of_bounded_bivariate_systems
-- name    : TranscendenceTheory.small_values_of_bounded_bivariate_systems
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T09:30:34.918712+00:00
-- url     : https://prove2.me/theorems/f098ad9b-a3a4-4733-9099-03c41bb77f4d
-- title:
--   Bounded polynomial coefficient selection and small-value transfer
-- statement:
--   Let $\theta,\nu\in\mathbb C$. Suppose there are $a,c>0$ such that every sufficiently large integer $N$ admits a bounded bivariate system at $(\theta,\nu)$: polynomial equations and test forms with the degree, height, dimension, and small-value properties in `BoundedBivariateSystem`.
--
--   Then there exist $A,c>0$ and, for every sufficiently large $N$, a polynomial $P_N\in\mathbb Z[X,Y]$ such that
--
--   $$
--   \deg_XP_N,\deg_YP_N\le AN,\qquad
--   |[X^kY^j]P_N|\le e^{AN},
--   $$
--
--   $$
--   0<|P_N(\theta,\nu)|\le e^{-cN^2\log N}.
--   $$
--
--   No algebraic independence or integrality assumption on $\theta,\nu$ is needed for this transfer. This isolates the finite coefficient-selection and polynomial-recombination step of the auxiliary-function argument. Constructing the systems, including their analytic estimates, is a separate hypothesis.
-- source:
--   Senthil Kumar K (2026), Section 3 Lemma 2 (coefficient expansion and Siegel lemma), Section 5 Lemma 8 (auxiliary coefficient selection), and Lemma 10 (linear combination of cleared derivative values). Explicit rectangular polynomial bounds replace field degree/type notation. The conclusion follows conditionally on bounded systems; their construction is not asserted here. https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2

import Definitions.Def_TranscendenceTheory_BoundedBivariateSystem

open scoped Polynomial
open Filter TranscendenceTheory

theorem TranscendenceTheory.small_values_of_bounded_bivariate_systems (θ ν : ℂ)
    (h_systems : ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in atTop, Nonempty (BoundedBivariateSystem θ ν a c N)) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ᶠ N : ℕ in atTop, ∃ P : ℤ[X][X],
        (P.natDegree : ℝ) ≤ A * N ∧
        (∀ j, ((P.coeff j).natDegree : ℝ) ≤ A * N) ∧
        (∀ j k, |((P.coeff j).coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
        P.eval₂ (Polynomial.aeval θ).toRingHom ν ≠ 0 ∧
        ‖P.eval₂ (Polynomial.aeval θ).toRingHom ν‖ ≤
          Real.exp (-c * (N : ℝ) ^ 2 * Real.log N) := by sorry
