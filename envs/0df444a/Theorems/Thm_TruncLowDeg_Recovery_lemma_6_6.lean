-- Prove2me | Theorems.Thm_TruncLowDeg_Recovery_lemma_6_6
-- name    : TruncLowDeg.Recovery.lemma_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:24:38.883206+00:00
-- url     : https://prove2.me/theorems/21af8af4-b6fc-469e-919d-1c5335a6da2a
-- title:
--   Lemma 6.6 — inverse perturbation: $A\succ0$, $\|\Sigma^{-1/2}\hat\Sigma\Sigma^{-1/2}-I\|_F\le2a\varepsilon_1$, $\|\Sigma^{-1/2}(\hat\mu-\mu)\|_2\le2\sqrt a(\varepsilon_2+R\varepsilon_1)$
-- statement:
--   Let $\mu\in\mathbb R^d$ with $\|\mu\|_2\le R$, and let $\Sigma\succ0$ with $\Sigma\preceq a\cdot I_d$. Let $A$ be a symmetric $d\times d$ matrix and $b\in\mathbb R^d$ with
--   $$\|A-\Sigma^{-1}\|_F\le\varepsilon_1,\qquad \|b-\Sigma^{-1}\mu\|_2\le\varepsilon_2,\qquad a\,\varepsilon_1\le1/2 .$$
--   Then $A\succ0$, and $\hat\Sigma=A^{-1}$, $\hat\mu=\hat\Sigma b$ satisfy
--   $$\|\Sigma^{-1/2}\hat\Sigma\Sigma^{-1/2}-I\|_F\le2a\varepsilon_1,\qquad \|\Sigma^{-1/2}(\hat\mu-\mu)\|_2\le2\sqrt a\,(\varepsilon_2+R\varepsilon_1).$$
--   It converts the entrywise estimates of Lemma 6.5 into the normalized parameter errors that control the total variation distance in Proposition 6.7.
--
--   Differences from the source:
--
--   - encoding: ℝ^d, coordinates j ∈ {1, …, d} → `Vec d = EuclideanSpace ℝ (Fin d)`, 0-based coordinates `Fin d`; reason: Lean convention; same instances
--   - encoding: Σ^{−1/2} → `invSqrt Σ = (CFC.sqrt Σ)⁻¹`, the inverse of the positive semidefinite square root; reason: Mathlib's square root, the one `multivariateGaussian` uses
--   - encoding: ‖·‖_F, Σ ⪯ a·I_d, A symmetric → `frob A = √(∑_{i,j} A_{ij}²)`, `LoewnerLE Σ (a • 1)` (a·I − Σ positive semidefinite), `A.IsSymm`; reason: the definitions
-- source:
--   Vári-Kakas, Wiedmer, A General Approach to Polynomial-Time Truncated Learning via Low-Degree Moments, STOC 2027 submission (manuscript sha256 613f0e39…), p. 28, Lemma 6.6; proof pp. 32–33 (§6.1.4)

import Definitions.Def_TruncLowDeg_Recovery_Basic

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TruncLowDeg.Recovery

/-- Lemma 6.6 (p. 28): inverse perturbation. Let `‖µ‖₂ ≤ R`, `Σ ≻ 0` with `Σ ⪯ a I`, `A`
symmetric and `b` a vector with `‖A − Σ⁻¹‖_F ≤ ε₁`, `‖b − Σ⁻¹µ‖₂ ≤ ε₂`, and `a ε₁ ≤ 1/2`.
Then `A ≻ 0`, and `Σ̂ = A⁻¹`, `µ̂ = Σ̂ b` satisfy `‖Σ^{−1/2} Σ̂ Σ^{−1/2} − I‖_F ≤ 2aε₁` and
`‖Σ^{−1/2}(µ̂ − µ)‖₂ ≤ 2√a (ε₂ + Rε₁)`. -/
theorem lemma_6_6 {d : ℕ} (μ : Vec d) (R : ℝ) (hμ : ‖μ‖ ≤ R) (Sig : Mat d)
    (hSig : Sig.PosDef) (a : ℝ) (ha : LoewnerLE Sig (a • (1 : Mat d))) (A : Mat d)
    (hA : A.IsSymm) (b : Vec d) (ε₁ ε₂ : ℝ) (h₁ : frob (A - Sig⁻¹) ≤ ε₁)
    (h₂ : ‖b - mulV Sig⁻¹ μ‖ ≤ ε₂) (hae : a * ε₁ ≤ 1 / 2) :
    A.PosDef ∧ frob (invSqrt Sig * A⁻¹ * invSqrt Sig - 1) ≤ 2 * a * ε₁ ∧
      ‖mulV (invSqrt Sig) (mulV A⁻¹ b - μ)‖ ≤ 2 * Real.sqrt a * (ε₂ + R * ε₁) := by sorry

end TruncLowDeg.Recovery
