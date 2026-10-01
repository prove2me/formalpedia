-- Prove2me | Theorems.Thm_RobustMDP_EntropyInner_dualFn_bounds
-- name    : RobustMDP.EntropyInner.dualFn_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:30:15.630553+00:00
-- url     : https://prove2.me/theorems/9ef37bd2-2ce7-4210-9cd8-71f58b0c92e8
-- title:
--   Eq. (48), p. 791 — $q^{\mathsf T}v+\beta\lambda\le\sigma(\lambda)\le v_{\max}+\beta\lambda$
-- statement:
--   Let $q\in\Delta_n$ with $q(j)>0$ for all $j$, let $\beta>0$ and $v\in\mathbb R^n$, and let $\sigma(\lambda)=\lambda\log\big(\sum_j q(j)e^{v(j)/\lambda}\big)+\beta\lambda$ be the dual function (47). Then for every $\lambda>0$,
--
--   $$
--   q^{\mathsf T}v+\beta\lambda \;\le\; \sigma(\lambda) \;\le\; v_{\max}+\beta\lambda,
--   $$
--
--   where $v_{\max}=\max_j v(j)$.
--
--   The two affine bounds give the starting bracket of the bisection algorithm that minimises $\sigma$.
--
--   **Formalization Note** The paper states (48) for all $\lambda\ge 0$ with the convention $\sigma(0)=v_{\max}$. At $\lambda=0$ both inequalities then read $q^{\mathsf T}v\le v_{\max}\le v_{\max}$, and the value $\sigma(0)=v_{\max}$ is the limit of Eq. (49) (a separate milestone). The statement here is for $\lambda>0$, where $\sigma$ is given by formula (47).
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 791, §6.3, Eq. (48); proof in Appendix C, p. 797

import Mathlib
import Definitions.Def_RobustMDP_EntropyInner_dualFunction

namespace RobustMDP.EntropyInner

/-- Eq. (48) (Nilim–El Ghaoui 2005, §6.3, p. 791; proof in Appendix C, p. 797). For `q ∈ Δₙ` with
`q > 0`, `β > 0` and every `λ > 0`,
`qᵀv + β λ ≤ σ(λ) ≤ v_max + β λ`, where `σ` is the dual function (47). -/
theorem dualFn_bounds {n : ℕ} (q v : Fin n → ℝ) (β : ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin n)) (hq_pos : ∀ j, 0 < q j) (hβ : 0 < β) :
    ∀ lam : ℝ, 0 < lam →
      (∑ j, q j * v j) + β * lam ≤ dualFn q v β lam ∧
      dualFn q v β lam ≤ vmax v + β * lam := by sorry

end RobustMDP.EntropyInner
