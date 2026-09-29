-- Prove2me | Theorems.Thm_Rudin_ch06_exists_singular_integrator
-- name    : Rudin.ch06_exists_singular_integrator
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T17:03:49.716826+00:00
-- url     : https://prove2.me/theorems/c88da336-b43c-4cca-bf0e-b90477b6d614
-- title:
--   Existence of a singular integrator: increasing, differentiable, derivative unbounded and with dense small values
-- statement:
--   A *singular integrator* is a function $\alpha : \mathbb{R} \to \mathbb{R}$ which is monotonically increasing, differentiable at every point of $[0,1]$, non-constant there, whose derivative is unbounded above on $[0,1]$ and satisfies
--
--   $$\inf_{x \in [u,v]} \alpha'(x) = 0 \qquad \text{for every } 0 \le u < v \le 1 ,$$
--
--   i.e. $\alpha'$ takes arbitrarily small values on every nondegenerate subinterval. This statement asserts that such a function exists.
--
--   The two requirements pull in opposite directions and both are needed. The dense small values are the feature of Pompeiu's function, a strictly increasing everywhere differentiable function whose derivative vanishes on a dense set, obtained as the inverse of $g(x) = \sum_n c_n (x - q_n)^{1/3}$ over an enumeration $(q_n)$ of the rationals: at a point where $g$ has infinite derivative the inverse has derivative $0$. Pompeiu's own function has bounded derivative, since $g' \ge \tfrac13 \sum_n c_n > 0$, so the unboundedness clause asks for a variant whose derivative also blows up, which can be arranged by kernels that flatten away from their singularity.
--
--   Note that the derivative cannot be unbounded on *every* subinterval: a derivative is of Baire class $1$, so its points of continuity are dense in every subinterval, and near such a point it is bounded. Unboundedness at a single point of $[0,1]$ is all that is asked for here.
--
--   The interest of the statement is that it decides the remaining unbounded statements of Rudin's Chapter 6: as recorded in `Rudin.ch06_singular_integrator_refutes`, a singular integrator refutes the versions of Theorems 6.17, 6.21 and 6.22 that omit the boundedness hypothesis, and conversely, if the derivative of the integrator is bounded, those theorems hold.
-- source:
--   D. Pompeiu, Sur les fonctions derivees, Mathematische Annalen 63 (1907), 326-332 (for the dense vanishing of the derivative); the statement here is the variant needed for Walter Rudin, Principles of Mathematical Analysis, 3rd edition, Chapter 6

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- There is a monotonically increasing function on `[0,1]`, differentiable at every point, which
is not constant, whose derivative is unbounded above and takes arbitrarily small values on every
nondegenerate subinterval. -/
theorem ch06_exists_singular_integrator :
    ∃ α : ℝ → ℝ, Monotone α ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1, HasDerivAt α (deriv α x) x) ∧
      α 0 < α 1 ∧
      (∀ K : ℝ, ∃ x ∈ Set.Icc (0:ℝ) 1, K < deriv α x) ∧
      (∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∀ ε > 0, ∃ x ∈ Set.Icc u v, deriv α x < ε) := by sorry

end Rudin
