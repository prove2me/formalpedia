-- Prove2me | Theorems.Thm_QAOAE3Lin2_Typical_variance_bound
-- name    : QAOAE3Lin2.Typical.variance_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:24.683035+00:00
-- url     : https://prove2.me/theorems/048d1084-8f89-40de-a666-68887264a624
-- title:
--   Section III, p. 11 — over the 2^m instances, the variance of the expected satisfied count is at most ¼m(6D + 3)(D + 1)
-- statement:
--   Let the triples form an E3LIN2 family with $m$ equations in which every bit lies in at most $D+1$ equations, and let $\gamma\in\mathbb R$. Draw the right-hand sides uniformly from $\{0,1\}^m$ and let $N$ be the expected number of equations satisfied when $|-\gamma,\pi/4\rangle$ is measured, a function of the instance. Then
--   $$\mathrm{Var}_d(N)\le\tfrac14\,m(6D+3)(D+1).$$
--
--   With $D$ fixed, the standard deviation over instances is $O(\sqrt m)$ while the mean is of order $m$; this is what makes the average-case bound (50) typical.
--
--   **Formalization Note** The variance is over the instances (the $d$'s), of the quantum expectation $N$; it is not the variance of the measurement outcome. $N$ and $\langle-\gamma,\pi/4|C|-\gamma,\pi/4\rangle$ differ by the constant $m/2$, so they have the same variance.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 11, Section III, the paragraph after (57)

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting

namespace QAOAE3Lin2.Typical

/-- p. 11: the variance over the `2^m` instances of the expected number of satisfied equations of
`|−γ, π/4⟩` is at most `¼ m (6D + 3)(D + 1)`. -/
theorem variance_bound {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (D : ℕ)
    (htri : QAOAE3Lin2.General.IsTripleFamily tri) (hocc : QAOAE3Lin2.General.BoundedOccurrence tri D) (γ : ℝ) :
    varD (fun rhs => QAOAE3Lin2.General.expSat tri rhs (-γ) (Real.pi / 4)) ≤
      (m : ℝ) * (6 * D + 3) * (D + 1) / 4 := by sorry

end QAOAE3Lin2.Typical
