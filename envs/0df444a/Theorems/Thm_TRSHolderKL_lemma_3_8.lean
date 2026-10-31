-- Prove2me | Theorems.Thm_TRSHolderKL_lemma_3_8
-- name    : TRSHolderKL.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:53:08.626982+00:00
-- url     : https://prove2.me/theorems/5d355e25-a84c-4451-af48-a44f0e9a8263
-- title:
--   Lemma 3.8 — error bound with modulus 1/2 in the easy case and hard case 1
-- statement:
--   Let $A$ be a nonzero real symmetric $n\times n$ matrix ($n\ge2$) and $b\in\mathbb R^n$, and suppose the TRS is in the easy case or in hard case 1 of Table 1 (in particular $\lambda_1<0$). Then there is $\tau>0$ such that
--   $$
--   \operatorname{dist}(x,S_0)\le\tau\big(f(x)-f^*+\delta_B(x)\big)^{1/2}\qquad\text{for all }x\in\mathbb R^n.
--   $$
--
--   Differences from the source:
--   - encoding: ℝⁿ; an n × n nonzero real symmetric matrix A; λ₁ the smallest eigenvalue → EuclideanSpace ℝ (Fin n); A : Matrix with A.IsHermitian and A ≠ 0 acting by Matrix.toEuclideanLin; lam1 A the least element of the real spectrum; reason: Lean conventions; the same instances
--   - encoding: for all x ∈ ℝⁿ, with δ_B(x) inside the right-hand side → for all x with ‖x‖ ≤ 1, δ_B dropped; reason: for ‖x‖ > 1 the paper's right-hand side is +∞ (δ_B = +∞), so the inequality is trivial there; on the ball δ_B = 0
--   - encoding: λ*, the Lagrange multiplier in the case definitions of Table 1 → some x* ∈ S₀ and λ* satisfy the KKT conditions of p.4; reason: for λ₁ < 0 the multiplier is the same for every optimal solution, so this is the table's λ*
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, Lemma 3.8, p.7

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_f
import Definitions.Def_TRSHolderKL_fstar
import Definitions.Def_TRSHolderKL_S0
import Definitions.Def_TRSHolderKL_EasyCase
import Definitions.Def_TRSHolderKL_HardCase1

open scoped InnerProductSpace
open RBMSensitivity (E)

namespace TRSHolderKL

/-- Lemma 3.8, Jiang and Li, arXiv:1911.11955v2, p.7. In the easy case or hard case 1, there
is `τ > 0` with `dist(x, S₀) ≤ τ (f(x) − f* + δ_B(x))^{1/2}` for all `x ∈ ℝⁿ`.

**Formalization Note.** The cases of Table 1 include `λ₁ < 0`. The inequality is stated for
`‖x‖ ≤ 1` (`δ_B(x) = 0`); outside `B` the right side is `+∞`. -/
theorem lemma_3_8 {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA0 : A ≠ 0) (b : E n) (hcase : EasyCase A b ∨ HardCase1 A b) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ x : E n, ‖x‖ ≤ 1 →
      Metric.infDist x (S0 A b) ≤ τ * (f A b x - fstar A b) ^ ((1 : ℝ) / 2) := by sorry

end TRSHolderKL
