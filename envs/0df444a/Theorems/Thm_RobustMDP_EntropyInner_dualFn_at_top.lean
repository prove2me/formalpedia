-- Prove2me | Theorems.Thm_RobustMDP_EntropyInner_dualFn_at_top
-- name    : RobustMDP.EntropyInner.dualFn_at_top
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:32:29.436837+00:00
-- url     : https://prove2.me/theorems/777d8b58-da01-47b9-8b6e-934041e51a7f
-- title:
--   Eq. (50), p. 791 — $\sigma(\lambda)=q^{\mathsf T}v+\beta\lambda+o(1)$ as $\lambda\to\infty$
-- statement:
--   Let $q\in\Delta_n$ with $q(j)>0$ for all $j$, let $\beta>0$ and $v\in\mathbb R^n$, and let $\sigma$ be the dual function (47). Then
--
--   $$
--   \sigma(\lambda)=q^{\mathsf T}v+\beta\lambda+o(1)\qquad(\lambda\to\infty),
--   $$
--
--   that is, $\sigma(\lambda)-(q^{\mathsf T}v+\beta\lambda)\to 0$.
--
--   Together with the lower bound in (48), this says the affine function $q^{\mathsf T}v+\beta\lambda$ is the asymptote of $\sigma$ at infinity.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 791, §6.3, Eq. (50); proof in Appendix C, p. 797

import Mathlib
import Definitions.Def_RobustMDP_EntropyInner_dualFunction
open Filter Topology

namespace RobustMDP.EntropyInner

/-- Eq. (50) (Nilim–El Ghaoui 2005, §6.3, p. 791; proof in Appendix C, p. 797). For `q ∈ Δₙ` with
`q > 0` and `β > 0`, as `λ → ∞`, `σ(λ) = qᵀv + βλ + o(1)`. -/
theorem dualFn_at_top {n : ℕ} (q v : Fin n → ℝ) (β : ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin n)) (hq_pos : ∀ j, 0 < q j) (hβ : 0 < β) :
    Tendsto (fun lam => dualFn q v β lam - ((∑ j, q j * v j) + β * lam)) atTop (𝓝 0) := by sorry

end RobustMDP.EntropyInner
