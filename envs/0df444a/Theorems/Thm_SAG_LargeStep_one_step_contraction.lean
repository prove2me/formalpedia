-- Prove2me | Theorems.Thm_SAG_LargeStep_one_step_contraction
-- name    : SAG.LargeStep.one_step_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:26:07.748799+00:00
-- url     : https://prove2.me/theorems/4edc9d0c-0bcb-42cb-8ce1-ac8c8fe1631d
-- title:
--   §A.6 Step 1 — for nμ/L ≥ 8, one SAG step with α = 1/(2nμ) contracts Q by the factor 1 − 1/(8n)
-- statement:
--   Throughout, $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ ($n\ge1$) are convex and differentiable with $L$-Lipschitz gradients $f_i'$, the average $g=\frac1n\sum_i f_i$ is $\mu$-strongly convex ($x\mapsto g(x)-\frac\mu2\|x\|^2$ is convex, $\mu>0$), $x^*$ minimizes $g$, $g'=\frac1n\sum_i f_i'$ and $\sigma^2=\frac1n\sum_i\|f_i'(x^*)\|^2$.
--
--   Assume $n\ge 8L/\mu$, i.e. $n\mu/L\ge8$. Let $Q$ be the Lyapunov function of §A.6 with $\alpha=\frac1{2n\mu}$, $\eta=2$, $\nu=\frac1{2n}$. For every SAG state $\theta^{k-1}=(y^{k-1},x^{k-1})$, if $\theta^k$ is obtained by one SAG step with step size $\alpha$ and a uniformly random index, then
--   $$\mathbb E\big[Q(\theta^k)\,\big|\,\mathcal F_{k-1}\big]\le\Big(1-\frac1{8n}\Big)Q(\theta^{k-1}).$$
--
--   This is the inequality $\mathbb E[Q(\theta^k)|\mathcal F_{k-1}]-(1-\delta)Q(\theta^{k-1})\le0$ established on pp. 24–28 for $\delta=\tilde\delta/n$ with the choice $\tilde\delta=\frac18$, for which the paper notes that $n\mu/L\ge8$ suffices.
--
--   **Formalization Note** The conditional expectation is the average over the $n$ indices of the step from an arbitrary fixed state; no reachability of the state is assumed.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, pp. 27–28, §A.6 Step 1

import Mathlib
import Definitions.Def_SAG_LargeStep_setting
import Definitions.Def_SAG_LargeStep_sagRun
import Definitions.Def_SAG_LargeStep_lyapunov

namespace SAG.LargeStep

/-- §A.6 Step 1, pp. 27–28: with `α = 1/(2nμ)`, `η = 2`, `ν = 1/(2n)`, `δ = 1/(8n)` and
`nμ/L ≥ 8`, for every state `θ`: `E[Q(θᵏ) | θᵏ⁻¹ = θ] ≤ (1 − 1/(8n)) Q(θ)`. -/
theorem one_step_contraction {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (h : Assumptions f f' L μ xstar)
    (hn : 8 * L / μ ≤ (n : ℝ))
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    (1 / (n : ℝ)) * ∑ i, lyap f f' (1 / (2 * (n : ℝ) * μ)) 2 (1 / (2 * (n : ℝ))) xstar
        (sagStep f' (1 / (2 * (n : ℝ) * μ)) θ i)
      ≤ (1 - 1 / (8 * (n : ℝ)))
        * lyap f f' (1 / (2 * (n : ℝ) * μ)) 2 (1 / (2 * (n : ℝ))) xstar θ := by sorry

end SAG.LargeStep
