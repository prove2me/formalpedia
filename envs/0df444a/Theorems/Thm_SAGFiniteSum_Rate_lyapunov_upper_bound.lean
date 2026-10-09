-- Prove2me | Theorems.Thm_SAGFiniteSum_Rate_lyapunov_upper_bound
-- name    : SAGFiniteSum.Rate.lyapunov_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:26.122263+00:00
-- url     : https://prove2.me/theorems/2fde526e-dd1f-4412-a1d7-3303feed9d40
-- title:
--   App. B.3, p. 41 — E[ℒ(θᵏ)|Fₖ₋₁] − (1 − δ)ℒ(θᵏ⁻¹) ≤ C₀‖xᵏ⁻¹ − x*‖² + C₁(xᵏ⁻¹ − x*)ᵀg′(xᵏ⁻¹) + C₂‖g′(xᵏ⁻¹)‖²
-- statement:
--   Assume the standing assumptions of §3 and that $g$ is $\mu$-strongly convex with $\mu\ge0$ ($x\mapsto g(x)-\frac\mu2\|x\|^2$ convex). Let $\mathcal L$ be the Lyapunov function of App. B.2 with parameters $a_1,a_2,b,c,d,h$, run SAG with step size $\alpha$, and let $\delta$ be a rate parameter, with $B_0,\dots,B_9$ and $C_0,C_1,C_2$ the coefficients of App. B.3. Suppose
--   1. $h\ge0$ and $0\le\delta\le1$;
--   2. $B_3>0$, $B_4>0$ and $\frac{B_6^2}{4B_3}+B_8\ge0$.
--
--   Then for every state $\theta^{k-1}=(y^{k-1},x^{k-1})$,
--   $$
--   \mathbb E\big[\mathcal L(\theta^k)\,\big|\,\mathcal F_{k-1}\big]-(1-\delta)\mathcal L(\theta^{k-1})\ \le\ C_0\|x^{k-1}-x^*\|^2+C_1(x^{k-1}-x^*)^\top g'(x^{k-1})+C_2\|g'(x^{k-1})\|^2 .
--   $$
--
--   This reduces the decrease of $\mathcal L$ to the sign conditions on $C_0,C_1,C_2$ collected in the constraints of B.5.
--
--   **Formalization Note** The conditional expectation is the average over the next index from an arbitrary state. The sign conditions are hypotheses the page uses without listing them together: $h\ge0$ is B.2's "for some $h\ge0$"; the page divides by $B_3,B_4$ after assuming them non-zero and maximizes over $y$ under "$B_3\ge0$ and $B_4\ge0$" (strict positivity is what the division needs); $\delta\le1$ and $h\ge0$ make the coefficient $(1-\delta)h$ of (12) non-negative; $B_0=2\delta h\ge0$ and $B_6^2/(4B_3)+B_8\ge0$ are needed where the page bounds $g(x)-g(x^*)$ and $\|f'(x)-f'(x^*)\|^2$ from above (the latter is assumed exactly, not through the stronger $B_8\ge0$). All hold for the B.5 constants.
-- source:
--   Schmidt, Le Roux & Bach, arXiv:1309.2388v2, App. B.3, pp. 40–41 (bound and C₀, C₁, C₂ on p. 41)

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model
import Definitions.Def_SAGFiniteSum_Rate_Lyapunov

open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- The B.3 upper bound (arXiv:1309.2388v2, App. B.3, p. 41). For the general Lyapunov function
`ℒ` of B.2 with parameters `P = (α, a₁, a₂, b, c, d, h, δ)`, run with step size `α`: if
`h ≥ 0`, `0 ≤ δ ≤ 1`, `B₃ > 0`, `B₄ > 0` and `B₆²/(4B₃) + B₈ ≥ 0`, then for every state `θ = (y, x)`,
`E[ℒ(θ⁺)] − (1 − δ)ℒ(θ) ≤ C₀‖x − x*‖² + C₁(x − x*)ᵀg'(x) + C₂‖g'(x)‖²`, the expectation being
the average over the next index. -/
theorem lyapunov_upper_bound {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hsc : ConvexOn ℝ Set.univ (fun x => SAGA.Convex.fAvg f x - μ / 2 * ‖x‖ ^ 2))
    (P : LyapParams) (hh : 0 ≤ P.h) (hδ0 : 0 ≤ P.δ) (hδ1 : P.δ ≤ 1)
    (hB3 : 0 < coefB3 n L P) (hB4 : 0 < coefB4 n L μ P)
    (hB68 : 0 ≤ coefB6 n L P ^ 2 / (4 * coefB3 n L P) + coefB8 n L P)
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    (1 / (n : ℝ)) * ∑ i, lyap f f' xstar P.a1 P.a2 P.b P.c P.d P.h (sagStep f' P.α i θ)
        - (1 - P.δ) * lyap f f' xstar P.a1 P.a2 P.b P.c P.d P.h θ
      ≤ coefC0 n L μ P * ‖θ.2 - xstar‖ ^ 2
        + coefC1 n L μ P * ⟪θ.2 - xstar, SAGA.Convex.gradAvg f' θ.2⟫
        + coefC2 n L μ P * ‖SAGA.Convex.gradAvg f' θ.2‖ ^ 2 := by sorry

end SAGFiniteSum.Rate
