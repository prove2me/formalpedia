-- Prove2me | Theorems.Thm_TRSHolderKL_theorem_3_13
-- name    : TRSHolderKL.theorem_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:53:32.004477+00:00
-- url     : https://prove2.me/theorems/cd1a5024-3866-4df6-b8b5-efb45bd91630
-- title:
--   Theorem 3.13 — Hölderian error bound for the TRS: modulus 1/4 in the TRS-ill case, 1/2 otherwise
-- statement:
--   Let $A$ be a nonzero real symmetric $n\times n$ matrix ($n\ge2$) and $b\in\mathbb R^n$. Then there is $\tau_{EB}>0$ such that
--   $$
--   \operatorname{dist}(x,S_0)\le\tau_{EB}\big(f(x)-f^*+\delta_B(x)\big)_+^{\rho}\qquad\text{for all }x\in\mathbb R^n,
--   $$
--   where $\rho=1/4$ in the TRS-ill case (24) ($\lambda_1\le0$, $b\in\mathrm{Range}(A-\lambda_1I)$, $\|(A-\lambda_1I)^\dagger b\|=1$) and $\rho=1/2$ otherwise.
--
--   This is the paper's global error bound; both exponents are part of the claim.
--
--   Differences from the source:
--   - encoding: ℝⁿ; an n × n nonzero real symmetric matrix A; λ₁ the smallest eigenvalue → EuclideanSpace ℝ (Fin n); A : Matrix with A.IsHermitian and A ≠ 0 acting by Matrix.toEuclideanLin; lam1 A the least element of the real spectrum; reason: Lean conventions; the same instances
--   - encoding: for all x ∈ ℝⁿ, with δ_B(x) inside the right-hand side → for all x with ‖x‖ ≤ 1, δ_B dropped; reason: for ‖x‖ > 1 the paper's right-hand side is +∞ (δ_B = +∞), so the inequality is trivial there; on the ball δ_B = 0
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Theorem 3.13, p.14

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_f
import Definitions.Def_TRSHolderKL_fstar
import Definitions.Def_TRSHolderKL_S0
import Definitions.Def_TRSHolderKL_TRSIll

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

open Classical in
/-- Theorem 3.13, Jiang and Li, arXiv:1911.11955v2, p.14. For the trust region subproblem
(P₀) there is `τ_EB > 0` with `dist(x, S₀) ≤ τ_EB (f(x) − f* + δ_B(x))₊^ρ` for all `x ∈ ℝⁿ`,
where `ρ = 1/4` in the TRS-ill case (24) and `ρ = 1/2` otherwise.

**Formalization Note.** Stated for `‖x‖ ≤ 1` (`δ_B(x) = 0`); outside `B` the right side is
`+∞`. `(·)₊ = max · 0`. -/
theorem theorem_3_13 {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA0 : A ≠ 0) (b : E n) :
    ∃ τEB : ℝ, 0 < τEB ∧ ∀ x : E n, ‖x‖ ≤ 1 →
      Metric.infDist x (S0 A b) ≤
        τEB * (max (f A b x - fstar A b) 0) ^ (if TRSIll A b then (1 : ℝ) / 4 else 1 / 2) := by sorry

end TRSHolderKL
