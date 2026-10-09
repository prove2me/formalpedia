-- Prove2me | Theorems.Thm_SAGFiniteSum_Rate_lyapunov_decrease
-- name    : SAGFiniteSum.Rate.lyapunov_decrease
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:19:27.738595+00:00
-- url     : https://prove2.me/theorems/f88741ee-d826-41c3-8860-d67acb27e248
-- title:
--   App. B.7, p. 46 — E(ℒ(θᵏ)|Fₖ₋₁) − (1 − δ)ℒ(θᵏ⁻¹) ≤ −(1/32n)(xᵏ⁻¹ − x*)ᵀg′(xᵏ⁻¹) ≤ 0
-- statement:
--   Assume the standing assumptions of §3 with $n\ge2$, and that $g$ is $\mu$-strongly convex with $\mu\ge0$. Let $\mathcal L$ be the Lyapunov function of App. B.2 with the constants of App. B.5 and $\delta=\min(\frac1{8n},\frac\mu{16L})$, and run SAG with step size $\alpha=\frac1{16L}$. Then for every state $\theta^{k-1}=(y^{k-1},x^{k-1})$,
--   $$
--   \mathbb E\big(\mathcal L(\theta^k)\,\big|\,\mathcal F_{k-1}\big)-(1-\delta)\mathcal L(\theta^{k-1})\ \le\ -\frac1{32n}(x^{k-1}-x^*)^\top g'(x^{k-1})\ \le\ 0 .
--   $$
--
--   This one-step contraction is the core of both rates of Theorem 1: with $\delta>0$ it gives the linear rate, and with $\delta=0$ it is summed to give the $O(n/k)$ rate.
--
--   **Formalization Note** The conditional expectation is the average over the next index from an arbitrary state. $n\ge2$ is the page's standing "$n>1$" of B.5 (at $n=1$, $h=-\frac12<0$). No hypothesis $\mu\le L$ is added: when $p\ge1$, $\mu$-strong convexity and $L$-Lipschitz gradients force $\mu\le L$, and when $p=0$ both sides vanish.
-- source:
--   Schmidt, Le Roux & Bach, arXiv:1309.2388v2, App. B.7, second display, p. 46

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model
import Definitions.Def_SAGFiniteSum_Rate_Lyapunov

open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- B.7, second display (arXiv:1309.2388v2, p. 46). With the B.5 constants, step size
`α = 1/(16L)`, `n ≥ 2` and `g` `μ`-strongly convex with `μ ≥ 0`, for every state `θ = (y, x)`:
`E[ℒ(θ⁺)] − (1 − δ)ℒ(θ) ≤ −(1/(32n))(x − x*)ᵀg'(x) ≤ 0`, the expectation being the average over
the next index. -/
theorem lyapunov_decrease {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar) (hn : 2 ≤ n)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hsc : ConvexOn ℝ Set.univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2))
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    (1 / (n : ℝ)) * ∑ i, sagLyap f f' L xstar (sagStep f' (1 / (16 * L)) i θ)
        - (1 - sagDelta n L μ) * sagLyap f f' L xstar θ
      ≤ -(1 / (32 * (n : ℝ))) * ⟪θ.2 - xstar, SAGA.Convex.gradAvg f' θ.2⟫
    ∧ -(1 / (32 * (n : ℝ))) * ⟪θ.2 - xstar, SAGA.Convex.gradAvg f' θ.2⟫ ≤ 0 := by sorry

end SAGFiniteSum.Rate
