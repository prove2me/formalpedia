-- Prove2me | Theorems.Thm_SAGFiniteSum_Rate_eq_13
-- name    : SAGFiniteSum.Rate.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:11.587692+00:00
-- url     : https://prove2.me/theorems/92be6668-e59f-4faa-a57d-48532671a068
-- title:
--   Eq. (13), p. 38 — E[2g(xᵏ + deᵀyᵏ) | Fₖ₋₁] bounded by L-smoothness of g and Lemma 1 with A = eeᵀ
-- statement:
--   Assume the standing assumptions of §3 ($f_i$ convex, differentiable, with $L$-Lipschitz gradients, $L>0$, $n\ge1$, $x^*$ a minimizer of $g$). Fix a step size $\alpha$, a scalar $d$ and a state $\theta^{k-1}=(y^{k-1},x^{k-1})$, and let $\theta^k=(y^k,x^k)$ be the state after one SAG step with index $i_k$ uniform on $\{1,\dots,n\}$. Write $u=y^{k-1}-f'(x^*)$ and $v=f'(x^{k-1})-f'(x^*)$. Then
--   $$
--   \begin{aligned}
--   \mathbb E\big[2g(x^k+de^\top y^k)\,\big|\,\mathcal F_{k-1}\big]
--   &\le 2g(x^{k-1})+2\big(d-\tfrac\alpha n\big)g'(x^{k-1})^\top\Big[\big(1-\tfrac1n\big)e^\top y^{k-1}+\tfrac1ne^\top f'(x^{k-1})\Big]\\
--   &\quad+L\big(d-\tfrac\alpha n\big)^2\,u^\top\Big[\big(1-\tfrac2n\big)ee^\top+\tfrac1nI\Big]u\\
--   &\quad+L\big(d-\tfrac\alpha n\big)^2\Big[\tfrac1n\|f'(x^{k-1})-f'(x^*)\|^2+\tfrac2n\,u^\top\big[ee^\top-I\big]v\Big].
--   \end{aligned}
--   $$
--
--   This bound is one of the two ingredients (with Lemma 1) of the upper bound on $\mathbb E[\mathcal L(\theta^k)\mid\mathcal F_{k-1}]-(1-\delta)\mathcal L(\theta^{k-1})$ in App. B.3.
--
--   **Formalization Note** The conditional expectation given $\mathcal F_{k-1}$ is the average $\frac1n\sum_i$ over the next index from an arbitrary state $\theta=(y,x)$. The block quadratic forms are written out: $u^\top ee^\top u=\|\sum_iu_i\|^2$, $u^\top u=\sum_i\|u_i\|^2$, $u^\top[ee^\top-I]v=\langle\sum_iu_i,\sum_iv_i\rangle-\sum_i\langle u_i,v_i\rangle$. The statement is the first line of the display bounded by its last expression; the middle line is a proof step. $\alpha$ and $d$ are free, as on the page.
-- source:
--   Schmidt, Le Roux & Bach, arXiv:1309.2388v2, App. B.3, Eq. (13), p. 38

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model

open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- Inequality (13) (arXiv:1309.2388v2, App. B.3, p. 38). Under the standing assumptions, for
every step size `α`, every `d` and every current state `θ = (y, x)`, the average over the next
index `i` of `2g(x⁺ + d eᵀy⁺)`, where `(y⁺, x⁺)` is the state after the SAG step with index `i`,
is at most
`2g(x) + 2(d − α/n) g'(x)ᵀ[(1 − 1/n)eᵀy + (1/n)eᵀf'(x)]
 + L(d − α/n)² uᵀ[(1 − 2/n)eeᵀ + (1/n)I]u
 + L(d − α/n)²[(1/n)‖f'(x) − f'(x*)‖² + (2/n) uᵀ[eeᵀ − I]v]`,
with `uᵢ = yᵢ − f'ᵢ(x*)` and `vᵢ = f'ᵢ(x) − f'ᵢ(x*)`. Here `uᵀeeᵀu = ‖∑ᵢ uᵢ‖²`,
`uᵀu = ∑ᵢ ‖uᵢ‖²` and `uᵀ[eeᵀ − I]v = ⟨∑ᵢ uᵢ, ∑ᵢ vᵢ⟩ − ∑ᵢ ⟨uᵢ, vᵢ⟩`. -/
theorem eq_13 {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar) (α d : ℝ)
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    (1 / (n : ℝ)) * ∑ i, 2 * SAGA.Convex.fAvg f
        ((sagStep f' α i θ).2 + d • ∑ j, (sagStep f' α i θ).1 j)
      ≤ 2 * SAGA.Convex.fAvg f θ.2
        + 2 * (d - α / (n : ℝ)) * ⟪SAGA.Convex.gradAvg f' θ.2,
            (1 - 1 / (n : ℝ)) • ∑ j, θ.1 j + (1 / (n : ℝ)) • ∑ j, f' j θ.2⟫
        + L * (d - α / (n : ℝ)) ^ 2 *
            ((1 - 2 / (n : ℝ)) * ‖∑ i, (θ.1 i - f' i xstar)‖ ^ 2
              + (1 / (n : ℝ)) * ∑ i, ‖θ.1 i - f' i xstar‖ ^ 2)
        + L * (d - α / (n : ℝ)) ^ 2 *
            ((1 / (n : ℝ)) * ∑ i, ‖f' i θ.2 - f' i xstar‖ ^ 2
              + (2 / (n : ℝ)) * (⟪∑ i, (θ.1 i - f' i xstar), ∑ i, (f' i θ.2 - f' i xstar)⟫
                - ∑ i, ⟪θ.1 i - f' i xstar, f' i θ.2 - f' i xstar⟫)) := by sorry

end SAGFiniteSum.Rate
