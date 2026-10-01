-- Prove2me | Theorems.Thm_RobustMDP_EntropyInner_mu_elimination
-- name    : RobustMDP.EntropyInner.mu_elimination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:31:24.53681+00:00
-- url     : https://prove2.me/theorems/3c0afbb4-b0d6-4cd6-a88a-cd2c509c4bf4
-- title:
--   §6.2, p. 791 — eliminating $\mu$: $\min_\mu d(\lambda,\mu)=\sigma(\lambda)$ of (47)
-- statement:
--   Let $q\in\Delta_n$ with $q(j)>0$ for all $j$, let $\beta>0$, $v\in\mathbb R^n$ and $\lambda>0$. Consider the two-variable dual objective
--
--   $$
--   d(\lambda,\mu)=\mu+\beta\lambda+\lambda\sum_j q(j)\exp\Big(\frac{v(j)-\mu}{\lambda}-1\Big),\qquad \mu\in\mathbb R,
--   $$
--
--   and put $\mu^*=\lambda\log\big(\sum_j q(j)\exp(v(j)/\lambda)\big)-\lambda$. Then
--
--   1. $\mu^*$ satisfies the optimality condition $\sum_j q(j)\exp\big(\frac{v(j)-\mu^*}{\lambda}-1\big)=1$;
--   2. $d(\lambda,\mu^*)=\sigma(\lambda)$, where $\sigma(\lambda)=\lambda\log\big(\sum_j q(j)e^{v(j)/\lambda}\big)+\beta\lambda$ is the function (47);
--   3. $\sigma(\lambda)$ is the minimum of $d(\lambda,\cdot)$ over $\mu\in\mathbb R$:
--   $$
--   \min_{\mu\in\mathbb R} d(\lambda,\mu)=\sigma(\lambda).
--   $$
--
--   This reduces the two-variable dual $\min_{\lambda>0,\mu} d(\lambda,\mu)$ of the inner problem to the one-dimensional problem $\min_{\lambda>0}\sigma(\lambda)$.
--
--   **Formalization Note** The minimum over $\mu$ is stated with `IsLeast` on the range of $\mu\mapsto d(\lambda,\mu)$, so it is both a lower bound and attained.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 791, §6.2, from "Setting the derivative with respect to μ to zero" to Eq. (47)

import Mathlib
import Definitions.Def_RobustMDP_EntropyInner_dualFunction

namespace RobustMDP.EntropyInner

/-- Elimination of `μ` in the dual of §6.2 (Nilim–El Ghaoui 2005, p. 791). For `q ∈ Δₙ` with
`q > 0`, `β > 0` and `λ > 0`, put `μ* = λ log (∑ⱼ q(j) exp (v(j)/λ)) − λ`. Then `μ*` satisfies
the optimality condition `∑ⱼ q(j) exp ((v(j) − μ*)/λ − 1) = 1`, and the minimum over `μ ∈ ℝ` of the
two-variable dual objective `d(λ, μ) = μ + βλ + λ ∑ⱼ q(j) exp ((v(j) − μ)/λ − 1)` equals `σ(λ)` of
(47) and is attained at `μ*`. -/
theorem mu_elimination {n : ℕ} (q v : Fin n → ℝ) (β : ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin n)) (hq_pos : ∀ j, 0 < q j) (hβ : 0 < β)
    (lam : ℝ) (hlam : 0 < lam) :
    (∑ j, q j * Real.exp
        ((v j - (lam * Real.log (∑ i, q i * Real.exp (v i / lam)) - lam)) / lam - 1)) = 1 ∧
    dualObj q v β lam (lam * Real.log (∑ i, q i * Real.exp (v i / lam)) - lam) =
        dualFn q v β lam ∧
    IsLeast (Set.range (fun mu : ℝ => dualObj q v β lam mu)) (dualFn q v β lam) := by sorry

end RobustMDP.EntropyInner
