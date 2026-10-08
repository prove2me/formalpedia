-- Prove2me | Theorems.Thm_SmoothedSimplex_TwoPhase_smoothed_complexity_polynomial
-- name    : SmoothedSimplex.TwoPhase.smoothed_complexity_polynomial
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:29:54.305588+00:00
-- url     : https://prove2.me/theorems/b1b2e73e-400e-443c-ae0b-4ef0e9793676
-- title:
--   Theorem 5.0.1 (Main) — polynomial smoothed simplex complexity
-- statement:
--   For the two-phase shadow-vertex simplex method, let $C(A,y,z)$ be the paper's Section 5 shadow-size bound on the expected number of pivots: $\mathbb E_{\mathcal I,\alpha}(S'_z+S_z^++2)$. There exist one polynomial $\mathcal P$ in three variables and one constant $\sigma_0>0$, uniform over all $n>d\ge3$, centers $\bar A,\bar y$, objectives $z$, and $\sigma>0$, such that
--   $$\mathbb E_{A,y}C(A,y,z)\le\min\!\left\{\mathcal P\!\left(d,n,\frac1{\min(\sigma,\sigma_0)}\right),\binom nd+\binom n{d+1}+2\right\}.$$
--   Each entry of $A,y$ is perturbed independently by Gaussian noise of standard deviation $\sigma\max_i\|(\bar y_i,\bar a_i)\|$. The centers have positive maximum norm so the paper's power-of-two normalization is defined. This theorem bounds a quantity that dominates the actual expected polar pivot count by Lemma 3.3.5.
--
--   **Formalization Note** The polynomial and $\sigma_0$ precede all dimensions and centers in the quantifier order. Integrability of the inner and outer costs is included in the conclusion to prevent Lean's default value for a nonintegrable Bochner integral from making the bound vacuous.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Theorem 5.0.1, printed p. 59, PDF p. 59

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

namespace SmoothedSimplex.TwoPhase

/-- Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7,
Theorem 5.0.1 (Main), printed p. 59, PDF p. 59. C is the §5 shadow-size upper bound on expected pivots; actual algorithmic pivots are at most C by Lemma 3.3.5. The normalization factor must be positive for the paper’s rescaling argument. Formalization Note: `[n]` is `Fin n`; all expectations use the specified probability laws. -/
theorem smoothed_complexity_polynomial :
    ∃ P : MvPolynomial (Fin 3) ℝ, ∃ σ₀ : ℝ, 0 < σ₀ ∧
    ∀ (n d : ℕ), 3 ≤ d → d < n →
    ∀ (c : Fin n → Point d) (b : Fin n → ℝ) (z : Point d)
      (σ : ℝ), 0 < σ → 0 < maxDataNorm c b →
      (∀ a : (Fin n → Point d) × (Fin n → ℝ),
        MeasureTheory.Integrable (fun p =>
          ((firstPhaseSteps a.1 a.2 z p.1 p.2 : ℝ) +
            (secondPhaseSteps a.1 a.2 z p.1 : ℝ) + 2)) (algorithmLaw n d)) ∧
      MeasureTheory.Integrable (fun a => complexityBound a.1 a.2 z)
        (gaussianInput c b (σ * maxDataNorm c b)) ∧
      (∫ a, complexityBound a.1 a.2 z
        ∂(gaussianInput c b (σ * maxDataNorm c b))) ≤
        min (MvPolynomial.eval ![(d : ℝ), (n : ℝ), 1 / min σ σ₀] P)
          ((Nat.choose n d : ℝ) + Nat.choose n (d + 1) + 2) := by sorry

end SmoothedSimplex.TwoPhase
