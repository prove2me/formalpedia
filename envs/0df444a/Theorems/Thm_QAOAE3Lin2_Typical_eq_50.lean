-- Prove2me | Theorems.Thm_QAOAE3Lin2_Typical_eq_50
-- name    : QAOAE3Lin2.Typical.eq_50
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:12.776542+00:00
-- url     : https://prove2.me/theorems/2a0d77f9-5584-4d75-a83e-1486d49b5d71
-- title:
--   Section III, (50), p. 10 — for γ ∈ [0, π/2], (m/2) sin γ cos^{3D} γ ⩽ E_d⟨−γ, π/4|C|−γ, π/4⟩ ⩽ (m/2) sin γ
-- statement:
--   Let the triples form an E3LIN2 family with $m$ equations in which every bit lies in at most $D+1$ equations, and let $0\le\gamma\le\pi/2$. Draw the right-hand sides uniformly from $\{0,1\}^m$ and measure $|-\gamma,\pi/4\rangle$. Then the average over the instances of the expected number of satisfied equations, minus $m/2$, satisfies
--   $$\frac m2\sin\gamma\cos^{3D}\gamma\;\le\;\mathbb E_d\big[\langle-\gamma,\pi/4|C|-\gamma,\pi/4\rangle\big]\;\le\;\frac m2\sin\gamma .$$
--
--   This is the mean performance of the level-one QAOA on a random-sign instance with fixed triples. Combined with the variance bound it yields the concentration statement of Section III.
--
--   **Formalization Note** $\langle-\gamma,\pi/4|C|-\gamma,\pi/4\rangle$ is the expected satisfied count minus $m/2$ (p. 4). The range $0\le\gamma\le\pi/2$ is added: the page leaves $\gamma$ unspecified at this point, but the lower bound needs $\sin\gamma\ge0$ and $\cos\gamma\ge0$, and the paper's choice $\gamma=1/(\sqrt3D^{1/2})$ lies in this range.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 10, Section III, (50)

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting

namespace QAOAE3Lin2.Typical

/-- (50), p. 10: for `γ ∈ [0, π/2]`, the average over the `2^m` instances of
`⟨−γ, π/4|C|−γ, π/4⟩` (the expected satisfied count minus `m/2`) lies between
`(m/2) sin γ cos^{3D} γ` and `(m/2) sin γ`. -/
theorem eq_50 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (D : ℕ) (htri : QAOAE3Lin2.General.IsTripleFamily tri)
    (hocc : QAOAE3Lin2.General.BoundedOccurrence tri D) (γ : ℝ) (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ Real.pi / 2) :
    (m : ℝ) / 2 * Real.sin γ * Real.cos γ ^ (3 * D) ≤
        avgD (fun rhs => QAOAE3Lin2.General.expSat tri rhs (-γ) (Real.pi / 4) - (m : ℝ) / 2) ∧
      avgD (fun rhs => QAOAE3Lin2.General.expSat tri rhs (-γ) (Real.pi / 4) - (m : ℝ) / 2) ≤
        (m : ℝ) / 2 * Real.sin γ := by sorry

end QAOAE3Lin2.Typical
