-- Prove2me | Theorems.Thm_RobustSDP_Uniqueness_dual_multiplier
-- name    : RobustSDP.Uniqueness.dual_multiplier
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:06:56.454378+00:00
-- url     : https://prove2.me/theorems/d77b7876-8419-4349-9bd8-c92be02b97bf
-- title:
--   Appendix A — the optimal dual matrix Z: Z ⪰ 0, Z ≠ 0, stationarity and τ²_opt Tr LLᵀZ = Tr R(x_opt)ᵀR(x_opt)Z
-- statement:
--   Assume $c \neq 0$, $F_0, \dots, F_m$ symmetric, and hypotheses H1, H2 and H3(a). Let $(x,\tau)$ be optimal for the SDP (15) (so $\tau > 0$). Then there is a matrix $Z \in \mathbb{R}^{n\times n}$, the dual variable of the constraint $G(y) \succeq 0$ of (16), such that
--
--   1. $Z \succeq 0$ and $Z \neq 0$;
--   2. (complementarity) $\operatorname{Tr} Z\, G(x,\tau) = 0$;
--   3. (stationarity in $x$) for $i = 1, \dots, m$,
--   $$\operatorname{Tr} Z\Bigl(F_i - \frac{1}{\tau}\bigl(R(x)^T R_i + R_i^T R(x)\bigr)\Bigr) = c_i ;$$
--   4. (stationarity in $\tau$)
--   $$\tau^2\, \operatorname{Tr} LL^T Z = \operatorname{Tr} R(x)^T R(x) Z .$$
--
--   The matrices in item 3 are the partial derivatives $\partial G/\partial x_i$ computed in Appendix A, and item 4 is $\operatorname{Tr} Z\, \partial G/\partial \tau = d_{m+1} = 0$ multiplied by $\tau^2$. These dual conditions are the input to the second-order argument that proves Theorem 4.2.
--
--   **Formalization Note** The paper's dual variable is $Y = \mathrm{diag}(Z, \mu)$ for (16), and it observes that $\mu = 0$ by complementarity; the statement gives $Z$ directly. Dual attainment is SDP strong duality under the Slater condition H1.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 49, Appendix A, first paragraph and displays; p. 48, Appendix A, opening paragraph

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix

namespace RobustSDP.Uniqueness

/-- Appendix A, p. 49: under `c ≠ 0`, H1, H2 and H3(a), at every optimal `(x, τ)` of (15) there is a
dual matrix `Z ⪰ 0`, `Z ≠ 0` (the multiplier of `G(y) ⪰ 0` in (16), with `μ = 0`) satisfying
complementarity `Tr Z G(y) = 0`, stationarity in `x`
(`Tr Z ∂G/∂xᵢ = cᵢ`, `∂G/∂xᵢ = Fᵢ − (1/τ)(R(x)ᵀRᵢ + RᵢᵀR(x))`), and, from stationarity in `τ`,
`τ² Tr LLᵀZ = Tr R(x)ᵀR(x)Z`. -/
theorem dual_multiplier {m n p q : ℕ} (D : SDPData m n p q) (c : Fin m → ℝ) (hc : c ≠ 0)
    (hsym : D.Symmetric) (h1 : D.Slater) (h2 : D.InfCompact c) (h3a : D.H3a)
    (x : Fin m → ℝ) (τ : ℝ) (hopt : D.IsOptimal c (x, τ)) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef ∧ Z ≠ 0 ∧
      (Z * D.G (x, τ)).trace = 0 ∧
      (∀ i : Fin m,
        (Z * (D.Fs i - τ⁻¹ • ((D.R x)ᵀ * D.Rs i + (D.Rs i)ᵀ * D.R x))).trace = c i) ∧
      τ ^ 2 * (D.L * D.Lᵀ * Z).trace = ((D.R x)ᵀ * D.R x * Z).trace := by sorry

end RobustSDP.Uniqueness
