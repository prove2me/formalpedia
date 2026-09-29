-- Prove2me | Theorems.Thm_RobustMDP_EntropyInner_kl_ball_inner_problem_dual
-- name    : RobustMDP.EntropyInner.kl_ball_inner_problem_dual
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:33:28.679282+00:00
-- url     : https://prove2.me/theorems/218f463b-966f-4c0b-ba8c-7e1d3c1735fe
-- title:
--   §6.2, Eq. (47), p. 791 — the worst-case expectation over a KL ball equals $\inf_{\lambda>0}\lambda\log\sum_j q(j)e^{v(j)/\lambda}+\beta\lambda$
-- statement:
--   Let $\Delta_n$ be the probability simplex of $\mathbb R^n$, let $q\in\Delta_n$ with $q(j)>0$ for every $j$, let $\beta>0$, and let $v\in\mathbb R^n$ be arbitrary. Consider the entropy uncertainty set $\mathcal P=\{p\in\Delta_n : D(p\|q)\le\beta\}$, where $D(p\|q)=\sum_j p(j)\log\frac{p(j)}{q(j)}$, and the inner problem (17)
--
--   $$
--   \sigma_{\mathcal P}(v)=\max_{p\in\mathcal P} v^{\mathsf T}p .
--   $$
--
--   Then the maximum is attained, and it equals the infimum of the one-dimensional convex function (47):
--
--   $$
--   \max_{p\in\mathcal P} v^{\mathsf T}p \;=\; \inf_{\lambda>0}\ \sigma(\lambda),\qquad \sigma(\lambda)=\lambda\log\Big(\sum_j q(j)\exp\frac{v(j)}{\lambda}\Big)+\beta\lambda .
--   $$
--
--   This is the tractability result for the entropy model: each step of the robust dynamic programming recursion with Kullback–Leibler uncertainty on the transition rows reduces to minimising a scalar convex function.
--
--   **Formalization Note** The statement asserts a real $s$ that is the greatest element of $\{p^{\mathsf T}v : p\in\mathcal P\}$ (`IsGreatest`) and the greatest lower bound of $\{\sigma(\lambda):\lambda>0\}$ (`IsGLB`). The paper writes $\min_{\lambda>0}\sigma(\lambda)$, but the minimum need not be attained: when $\beta\ge-\log Q(v)$ the infimum $v_{\max}$ is only approached as $\lambda\to0^+$ (paper p. 792), so the dual side is an infimum with the paper's $\sigma(0):=v_{\max}$ as its limit value. No restriction is placed on $v$: in particular the "without loss of generality $v\in\mathbb R^n_+$" of the paper's §5 is not assumed.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 791, §6.2, Eq. (47) (inner problem (17), p. 784)

import Mathlib
import Definitions.Def_RobustMDP_EntropyInner_klBall
import Definitions.Def_RobustMDP_EntropyInner_dualFunction

namespace RobustMDP.EntropyInner

/-- §6.2, Eq. (47) (Nilim–El Ghaoui 2005, p. 791): the dual of the inner problem (17) for the
entropy model. Let `q ∈ Δₙ` with `q > 0`, `β > 0`, and `v ∈ ℝⁿ` arbitrary. The inner problem
`σ_𝒫(v) = max_{p ∈ 𝒫} pᵀv` over `𝒫 = {p ∈ Δₙ : D(p‖q) ≤ β}` has an attained maximum, and this
maximum equals the infimum over `λ > 0` of the convex one-dimensional function
`σ(λ) = λ log (∑ⱼ q(j) exp (v(j)/λ)) + βλ`. -/
theorem kl_ball_inner_problem_dual {n : ℕ} (q v : Fin n → ℝ) (β : ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin n)) (hq_pos : ∀ j, 0 < q j) (hβ : 0 < β) :
    ∃ s : ℝ,
      IsGreatest ((fun p : Fin n → ℝ => ∑ j, p j * v j) '' klBall q β) s ∧
      IsGLB ((fun lam => dualFn q v β lam) '' Set.Ioi 0) s := by sorry

end RobustMDP.EntropyInner
