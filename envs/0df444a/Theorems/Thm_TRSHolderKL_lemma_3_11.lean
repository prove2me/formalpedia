-- Prove2me | Theorems.Thm_TRSHolderKL_lemma_3_11
-- name    : TRSHolderKL.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:53:26.4325+00:00
-- url     : https://prove2.me/theorems/b5e96c01-10ec-4304-9102-b599ff98c528
-- title:
--   Lemma 3.11 — $\operatorname{dist}(x,S_1)+\sqrt{1-\|x\|^2}\ge\operatorname{dist}(x,S_0)\sin\gamma$ in hard case 2 (ii)
-- statement:
--   Let $A$ be a nonzero real symmetric $n\times n$ matrix ($n\ge2$) and $b\in\mathbb R^n$ in hard case 2 (ii), and let $\bar x=(A-\lambda_1I)^\dagger b$. Then there is $\gamma\in(0,\pi/2)$ with
--   $$
--   \sin\gamma=\frac{1-\|\bar x\|}{\sqrt{(1-\|\bar x\|)^2+1-\|\bar x\|^2}}
--   $$
--   such that
--   $$
--   \operatorname{dist}(x,S_1)+\sqrt{1-\|x\|^2}\ \ge\ \operatorname{dist}(x,S_0)\sin\gamma\qquad\text{for all }x\text{ with }\|x\|\le1 .
--   $$
--
--   Differences from the source:
--   - encoding: ℝⁿ; an n × n nonzero real symmetric matrix A; λ₁ the smallest eigenvalue → EuclideanSpace ℝ (Fin n); A : Matrix with A.IsHermitian and A ≠ 0 acting by Matrix.toEuclideanLin; lam1 A the least element of the real spectrum; reason: Lean conventions; the same instances
--   - encoding: λ*, the Lagrange multiplier in the case definitions of Table 1 → some x* ∈ S₀ and λ* satisfy the KKT conditions of p.4; reason: for λ₁ < 0 the multiplier is the same for every optimal solution, so this is the table's λ*
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Lemma 3.11, display (11), p.9

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_S0
import Definitions.Def_TRSHolderKL_S1
import Definitions.Def_TRSHolderKL_xbar
import Definitions.Def_TRSHolderKL_HardCase2ii

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

/-- Lemma 3.11, Jiang and Li, arXiv:1911.11955v2, display (11), p.9. In hard case 2 (ii),
there is `γ ∈ (0, π/2)` with `sin γ = (1 − ‖x̄‖)/√((1 − ‖x̄‖)² + 1 − ‖x̄‖²)` such that
`dist(x, S₁) + √(1 − ‖x‖²) ≥ dist(x, S₀) sin γ` for all `x` with `‖x‖ ≤ 1`. -/
theorem lemma_3_11 {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA0 : A ≠ 0) (b : E n) (hcase : HardCase2ii A b) :
    ∃ γ : ℝ, 0 < γ ∧ γ < Real.pi / 2 ∧
      Real.sin γ = (1 - ‖xbar A b‖) /
        Real.sqrt ((1 - ‖xbar A b‖) ^ 2 + 1 - ‖xbar A b‖ ^ 2) ∧
      ∀ x : E n, ‖x‖ ≤ 1 →
        Metric.infDist x (S0 A b) * Real.sin γ ≤
          Metric.infDist x (S1 A b) + Real.sqrt (1 - ‖x‖ ^ 2) := by sorry

end TRSHolderKL
