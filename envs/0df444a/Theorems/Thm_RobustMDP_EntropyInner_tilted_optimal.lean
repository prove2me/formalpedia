-- Prove2me | Theorems.Thm_RobustMDP_EntropyInner_tilted_optimal
-- name    : RobustMDP.EntropyInner.tilted_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:30:55.093094+00:00
-- url     : https://prove2.me/theorems/ef61bbf2-5da5-4c13-8c40-b39616d51f08
-- title:
--   §6.2, p. 791 — the optimal distribution $p^*\propto q(j)e^{v(j)/\lambda}$ (Gibbs variational principle)
-- statement:
--   Let $q\in\Delta_n$ with $q(j)>0$ for all $j$, let $v\in\mathbb R^n$ and $\lambda>0$.
--
--   1. For every $p\in\Delta_n$,
--   $$
--   p^{\mathsf T}v-\lambda D(p\|q) \;\le\; \lambda\log\Big(\sum_j q(j)\exp\frac{v(j)}{\lambda}\Big).
--   $$
--   2. The tilted distribution
--   $$
--   p^*(j)=\frac{q(j)\exp(v(j)/\lambda)}{\sum_i q(i)\exp(v(i)/\lambda)}
--   $$
--   belongs to $\Delta_n$ and attains equality in 1.
--
--   In words, $p^*$ maximises the penalised objective $p^{\mathsf T}v-\lambda D(p\|q)$ over the simplex, and the maximum is $\lambda$ times the log-moment-generating function of $v$ under $q$ at $1/\lambda$. This is what makes $p^*$ the optimal distribution for a given multiplier $\lambda$ in the dual of the inner problem.
--
--   **Formalization Note** The paper only displays the formula for $p^*$ ("The optimal distribution is"); the inequality in 1 with equality at $p^*$ is the content that display relies on.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 791, §6.2, display "The optimal distribution is p* = …"

import Mathlib
import Definitions.Def_RobustMDP_EntropyInner_klBall
import Definitions.Def_RobustMDP_EntropyInner_dualFunction

namespace RobustMDP.EntropyInner

/-- The optimal distribution of §6.2 (Nilim–El Ghaoui 2005, p. 791), in variational form.
For `q ∈ Δₙ` with `q > 0` and `λ > 0`:
(a) every `p ∈ Δₙ` satisfies `pᵀv − λ D(p‖q) ≤ λ log ∑ⱼ q(j) exp (v(j)/λ)`;
(b) the tilted distribution `p*(j) = q(j) exp (v(j)/λ) / ∑ᵢ q(i) exp (v(i)/λ)` lies in `Δₙ` and
attains equality in (a). -/
theorem tilted_optimal {n : ℕ} (q v : Fin n → ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin n)) (hq_pos : ∀ j, 0 < q j) (lam : ℝ) (hlam : 0 < lam) :
    (∀ p ∈ stdSimplex ℝ (Fin n),
      (∑ j, p j * v j) - lam * klDiv p q ≤
        lam * Real.log (∑ j, q j * Real.exp (v j / lam))) ∧
    tiltedDist q v lam ∈ stdSimplex ℝ (Fin n) ∧
    (∑ j, tiltedDist q v lam j * v j) - lam * klDiv (tiltedDist q v lam) q =
        lam * Real.log (∑ j, q j * Real.exp (v j / lam)) := by sorry

end RobustMDP.EntropyInner
