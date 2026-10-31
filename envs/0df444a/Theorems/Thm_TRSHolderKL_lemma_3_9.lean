-- Prove2me | Theorems.Thm_TRSHolderKL_lemma_3_9
-- name    : TRSHolderKL.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:53:46.587335+00:00
-- url     : https://prove2.me/theorems/75eabdca-8640-47df-800e-c235999ec77e
-- title:
--   Lemma 3.9 — error bound with modulus 1/4 in hard case 2 (i)
-- statement:
--   Let $A$ be a nonzero real symmetric $n\times n$ matrix ($n\ge2$) and $b\in\mathbb R^n$, and suppose the TRS is in hard case 2 (i) of Table 1. Then there is $\tau>0$ such that
--   $$
--   \operatorname{dist}(x,S_0)\le\tau\big(f(x)-f^*+\delta_B(x)\big)^{1/4}\qquad\text{for all }x\in\mathbb R^n.
--   $$
--   Hard case 2 (i) is the nonconvex part of the TRS-ill case.
--
--   Differences from the source:
--   - encoding: ℝⁿ; an n × n nonzero real symmetric matrix A; λ₁ the smallest eigenvalue → EuclideanSpace ℝ (Fin n); A : Matrix with A.IsHermitian and A ≠ 0 acting by Matrix.toEuclideanLin; lam1 A the least element of the real spectrum; reason: Lean conventions; the same instances
--   - encoding: for all x ∈ ℝⁿ, with δ_B(x) inside the right-hand side → for all x with ‖x‖ ≤ 1, δ_B dropped; reason: for ‖x‖ > 1 the paper's right-hand side is +∞ (δ_B = +∞), so the inequality is trivial there; on the ball δ_B = 0
--   - encoding: λ*, the Lagrange multiplier in the case definitions of Table 1 → some x* ∈ S₀ and λ* satisfy the KKT conditions of p.4; reason: for λ₁ < 0 the multiplier is the same for every optimal solution, so this is the table's λ*
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Lemma 3.9, p.8

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_f
import Definitions.Def_TRSHolderKL_fstar
import Definitions.Def_TRSHolderKL_S0
import Definitions.Def_TRSHolderKL_HardCase2i

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

/-- Lemma 3.9, Jiang and Li, arXiv:1911.11955v2, p.8. In hard case 2 (i), there is `τ > 0`
with `dist(x, S₀) ≤ τ (f(x) − f* + δ_B(x))^{1/4}` for all `x ∈ ℝⁿ`.

**Formalization Note.** Stated for `‖x‖ ≤ 1` (`δ_B(x) = 0`); outside `B` the right side is
`+∞`. -/
theorem lemma_3_9 {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA0 : A ≠ 0) (b : E n) (hcase : HardCase2i A b) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ x : E n, ‖x‖ ≤ 1 →
      Metric.infDist x (S0 A b) ≤ τ * (f A b x - fstar A b) ^ ((1 : ℝ) / 4) := by sorry

end TRSHolderKL
