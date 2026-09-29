-- Prove2me | Theorems.Thm_StochasticProg_Recourse_thm6a_Q_lipschitz_convex_finite
-- name    : StochasticProg.Recourse.thm6a_Q_lipschitz_convex_finite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T04:47:33.433074+00:00
-- url     : https://prove2.me/theorems/dd4055b1-61d9-4377-b043-912a2c456959
-- title:
--   Chapter 3, Theorem 6(a) -- Q is Lipschitzian, convex and finite on K2
-- statement:
--   **Chapter 3, Theorem 6(a).** For a stochastic program with fixed recourse and a finite scenario
--   set, $Q$ is finite on $K_2$, and its restriction to $K_2$ is a Lipschitzian convex function: there
--   is $L \ge 0$ with $|Q(x) - Q(x')| \le L\lVert x - x'\rVert$ for all $x, x' \in K_2$.
--
--   Convexity of $Q$ is what makes the deterministic-equivalent objective $c^{\mathsf T}x + Q(x)$ a
--   convex program, and the Lipschitz bound is what licenses the subgradient existence used by
--   Theorem 9.
--
--   **Formalization Note.** The book cites the Lipschitz bound to Wets [1972] and Kall [1976] without
--   giving the proof (finiteness and convexity are called "immediate" but the Lipschitz constant is
--   not constructed), so this milestone is *stated*, not *derived* from the second-stage LP's
--   structure, and its Lean proof is expected to stay `sorry`.
--
--   **Moderator's note.** The book's standing assumption for §3.1c–e (p. 112: "assuming it is not −∞") is stated explicitly: no second-stage problem is unbounded below (`Q(x, ξ_k) ≠ −∞` for every `x` and scenario `k`; for the abstract `Q` of Corollary 10, `Q x ≠ −∞`). Without it "finite on K₂" and the KKT characterisation can fail.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 112, Chapter 3, Theorem 6(a)

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance

namespace StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- Chapter 3, Theorem 6(a) (p. 112): for a stochastic program with fixed recourse
and a finite scenario set, `Q` is finite on `K2`, and (its real-valued restriction
to `K2` is) a Lipschitzian convex function. The book cites the Lipschitz bound to
Wets [1972]/Kall [1976] without proof, so this milestone is stated, not derived. -/
theorem thm6a_Q_lipschitz_convex_finite (inst : Instance n1 n2 m1 m2 K)
    (hQ : ∀ x k, QVal inst x k ≠ ⊥) :
    (∀ x ∈ K2 inst, ∃ r : ℝ, Q inst x = (r : EReal)) ∧
      ConvexOn ℝ (K2 inst) (fun x => (Q inst x).toReal) ∧
      ∃ L : NNReal, LipschitzOnWith L (fun x => (Q inst x).toReal) (K2 inst) := by sorry

end StochasticProg.Recourse
