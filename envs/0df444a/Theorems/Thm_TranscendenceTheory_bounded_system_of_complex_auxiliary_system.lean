-- Prove2me | Theorems.Thm_TranscendenceTheory_bounded_system_of_complex_auxiliary_system
-- name    : TranscendenceTheory.bounded_system_of_complex_auxiliary_system
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T09:51:52.452629+00:00
-- url     : https://prove2.me/theorems/b7a6408b-454b-4273-b8ea-3a53f83306a9
-- title:
--   Transfer from bounded complex coefficients to polynomial auxiliary systems
-- statement:
--   Fix $\theta,\nu\in\mathbb C$ and $g\in\mathbb Z[X,Y]$ such that every polynomial vanishing at $(\theta,\nu)$ is divisible by $g$. Let $a,c\in\mathbb R$ and $N\in\mathbb N$.
--
--   Suppose a complex auxiliary system $S$ at $(\theta,\nu)$ has arithmetic exponent $aN$, complex coefficient exponent $bN$, and small-value exponent $-cN^2\log N$, where
--
--   $$
--   b=(3+|\theta|+|\nu|)a.
--   $$
--
--   Assume its outer degree bound $E$ satisfies $E<\deg_Yg$. Then
--
--   $$
--   \text{there exists a bounded bivariate system at }(\theta,\nu,a,c,N).
--   $$
--
--   Thus the same equations and test forms satisfy the polynomial-vector small-value requirement of `BoundedBivariateSystem`. Reducedness ensures nonvanishing after evaluation, while the size, degree, and coefficient bounds give the required complex coefficient bound. This transfers an analytic estimate for bounded complex vectors to the interface used by integer Siegel selection.
--
--   **Formalization Note.** This is a single-$N$ statement and does not require positive $a,c$. Positivity is imposed by the mission's eventual system-existence theorem. It assumes the complex system's analytic estimate and does not establish that estimate.
-- source:
--   Interface transfer in the auxiliary-function proof of Senthil Kumar K (2026): Section 3 reduced coefficients; Section 5 Lemma 8 and equation (29) for the vanishing equations; Lemma 6 for bounds in terms of complex coefficients, Lemma 9 for nonvanishing, and equations (34)-(35) with Lemma 10 for small cleared values. The explicit constant (3+|theta|+|nu|)a is derived from elementary polynomial evaluation and is not a quoted source constant. https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2

import Definitions.Def_TranscendenceTheory_BoundedBivariateSystem
import Definitions.Def_TranscendenceTheory_ComplexAuxiliarySystem

open Polynomial TranscendenceTheory
open scoped Polynomial

theorem TranscendenceTheory.bounded_system_of_complex_auxiliary_system (θ ν : ℂ) (g : ℤ[X][X])
    (hker : ∀ p : ℤ[X][X], p.eval₂ (aeval θ).toRingHom ν = 0 → g ∣ p)
    (a c : ℝ) (N : ℕ)
    (S : ComplexAuxiliarySystem θ ν a ((3 + ‖θ‖ + ‖ν‖) * a) c N)
    (hred : S.yDegree < g.natDegree) :
    Nonempty (BoundedBivariateSystem θ ν a c N) := by sorry
