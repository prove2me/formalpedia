-- Prove2me | Theorems.Thm_StochasticProg_Recourse_thm9_kkt_optimality
-- name    : StochasticProg.Recourse.thm9_kkt_optimality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T04:48:49.408734+00:00
-- url     : https://prove2.me/theorems/a463dec7-0a6a-46c4-83bc-481be36fdddf
-- title:
--   Chapter 3, Theorem 9 -- KKT optimality condition for the two-stage recourse LP
-- statement:
--   **Chapter 3, Theorem 9 (goal theorem).** Suppose the deterministic-equivalent program (1.2) --
--   minimize $z(x) = c^{\mathsf T}x + Q(x)$ over $K_1 = \{x \mid Ax=b,\ x\ge 0\}$ -- has a finite
--   optimal value. A point $x^* \in K_1$ is optimal if and only if there exist $\lambda^* \in
--   \mathbb{R}^{m_1}$ and $\mu^* \in \mathbb{R}^{n_1}_{\ge 0}$ with $(\mu^*)^{\mathsf T}x^* = 0$
--   such that
--   $$-c + A^{\mathsf T}\lambda^* + \mu^* \in \partial Q(x^*).$$
--
--   This is the KKT-style optimality condition for the two-stage stochastic linear program with fixed
--   recourse: it combines the subdifferential of the convex, possibly nondifferentiable recourse
--   function $Q$ (Theorem 6) with the ordinary linear-programming complementarity condition for the
--   polyhedral constraint set $K_1$.
--
--   **Formalization Note.** "Optimal in (1.2)" is formalized as attaining the infimum of $z$ over
--   $K_1$, i.e. $z(x^*) = \inf_{x \in K_1} z(x)$, using the extended-real-valued `sInf`; "finite
--   optimal value" is the hypothesis that this infimum equals some real $z_0$, exactly as the theorem
--   statement presupposes. $\partial Q(x^*)$ is `StochasticProg.Recourse.subdiffQ`.
--
--   **Moderator's note.** The book's standing assumption for §3.1c–e (p. 112: "assuming it is not −∞") is stated explicitly: no second-stage problem is unbounded below (`Q(x, ξ_k) ≠ −∞` for every `x` and scenario `k`; for the abstract `Q` of Corollary 10, `Q x ≠ −∞`). Without it "finite on K₂" and the KKT characterisation can fail.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 116, Chapter 3, Theorem 9

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_Recourse_Subdiff

namespace StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- Chapter 3, Theorem 9 (p. 116), the goal theorem: suppose the deterministic
equivalent problem (1.2) has a finite optimal value. A solution `x* ∈ K1` is
optimal if and only if there exist `λ* ∈ ℝ^{m1}` and `μ* ∈ ℝ^{n1}_+` with
`(μ*)ᵀx* = 0` such that `-c + Aᵀλ* + μ* ∈ ∂Q(x*)` (Eq. (1.12)). -/
theorem thm9_kkt_optimality (inst : Instance n1 n2 m1 m2 K)
    (hQ : ∀ x k, QVal inst x k ≠ ⊥)
    (hfin : ∃ z0 : ℝ, sInf (obj inst '' K1 inst) = (z0 : EReal))
    (xstar : Fin n1 → ℝ) (hx : xstar ∈ K1 inst) :
    (obj inst xstar = sInf (obj inst '' K1 inst)) ↔
      ∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ),
        (∀ i, 0 ≤ mu i) ∧ dotProduct mu xstar = 0 ∧
        (fun j => -inst.c j + Matrix.mulVec (Matrix.transpose inst.A) lam j + mu j) ∈
          subdiffQ inst xstar := by sorry

end StochasticProg.Recourse
