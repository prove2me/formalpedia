-- Prove2me | Theorems.Thm_RobustMDP_EntropyInner_lambda_zero_optimal
-- name    : RobustMDP.EntropyInner.lambda_zero_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:32:53.532544+00:00
-- url     : https://prove2.me/theorems/7ff7934f-b033-4fd1-8ed7-fa4fc92392a3
-- title:
--   §6.3, p. 792 — if $\beta\ge-\log Q(v)$ then $\lambda=0$ is optimal and the value is $v_{\max}$
-- statement:
--   Let $q\in\Delta_n$ with $q(j)>0$ for all $j$, let $\beta>0$ and $v\in\mathbb R^n$, and let $\sigma$ be the dual function (47), $v_{\max}=\max_j v(j)$ and $Q(v)=\sum_{j:\,v(j)=v_{\max}}q(j)$. If
--
--   $$
--   \beta \;\ge\; -\log Q(v)
--   $$
--
--   (equivalently $\sigma'(0)=\beta+\log Q(v)\ge 0$), then
--
--   1. $\inf_{\lambda>0}\sigma(\lambda)=v_{\max}$, so $\lambda=0$ is optimal for the dual;
--   2. the worst-case value of $p^{\mathsf T}v$ over $\mathcal P=\{p\in\Delta_n : D(p\|q)\le\beta\}$ is $v_{\max}$, and it is attained.
--
--   For such $\beta$ robustness disregards the prior information carried by $q$. Unlike the threshold $\max_i(-\log q_i)$ of §6.1, the threshold $-\log Q(v)$ depends on $v$.
--
--   **Formalization Note** The infimum is stated with `IsGLB` over $\{\sigma(\lambda):\lambda>0\}$; it is not attained at any $\lambda>0$ in general, which is why the paper speaks of $\lambda=0$. The paper's first sentence has the non-strict condition $\sigma'(0)\ge 0$ and its second sentence the strict $\beta>-\log Q(v)$; the statement here uses the non-strict version, which contains both.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 792, §6.3, second paragraph

import Mathlib
import Definitions.Def_RobustMDP_EntropyInner_klBall
import Definitions.Def_RobustMDP_EntropyInner_dualFunction

namespace RobustMDP.EntropyInner

/-- §6.3 (Nilim–El Ghaoui 2005, p. 792). For `q ∈ Δₙ` with `q > 0` and `β > 0`: if
`β ≥ −log Q(v)` (equivalently `σ'(0) = β + log Q(v) ≥ 0`), then `λ = 0` is optimal for the dual:
the infimum of `σ` over `λ > 0` is `v_max`, and the worst-case value of `pᵀv` over the entropy set
`𝒫 = {p ∈ Δₙ : D(p‖q) ≤ β}` is `v_max` (attained). -/
theorem lambda_zero_optimal {n : ℕ} (q v : Fin n → ℝ) (β : ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin n)) (hq_pos : ∀ j, 0 < q j) (hβ : 0 < β)
    (hβQ : -Real.log (maxMass q v) ≤ β) :
    IsGLB ((fun lam => dualFn q v β lam) '' Set.Ioi 0) (vmax v) ∧
    IsGreatest ((fun p : Fin n → ℝ => ∑ j, p j * v j) '' klBall q β) (vmax v) := by sorry

end RobustMDP.EntropyInner
