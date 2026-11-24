-- Prove2me | Theorems.Thm_RegMT_Classif_Supplement_theorem_3_30
-- name    : RegMT.Classif.Supplement.theorem_3_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:36:18.860007+00:00
-- url     : https://prove2.me/theorems/c759be8b-46f5-440f-b5a0-846179c7f675
-- title:
--   Theorem 3.30 — neural regularization (corrected: output norm)
-- statement:
--   Let $M,N\ge1$. Consider every weight collection in an $M$-layer network with continuous vector activations and arbitrary finite-dimensional layer norms, and a nonnegative convex Lipschitz univariate loss. Let $o:E_M\to\mathbb R$ be the final scalar coordinate map, and put $a(W)=\prod_m\operatorname{lip}(\sigma_m)\|W_m\|$. For either task, all $\rho\ge0$ and $0<\kappa\le\infty$, the corrected arbitrary-output-norm estimate is
--   $$\inf_W\sup_{Q\in B_\rho(\hat P_N)}\mathbb E_Q\ell(h_W(x),y)\le\inf_W\left[\frac1N\sum_i\ell(h_W(\hat x_i),\hat y_i)+\rho\operatorname{lip}(L)\max\{\|o\|a(W),c/\kappa\}\right].$$
--   Regression uses (11) and $c=1$; classification uses (16) and $c=\max\{1,2\sup_{W,x\in X}|h_W(x)|\}$. Activation moduli and the global supremum may be infinite. Every $\|W_m\|$ is the actual operator norm between the adjacent layer norms. With the usual absolute-value final norm, $\|o\|=1$ and the displayed expression is exactly (34). For arbitrary output scaling the source omits this necessary conversion factor; DISPROOF.md gives an optimized one-layer counterexample. No bounded-network assumption or activation modulus normalization is added.
--
--   Differences from the source:
--   - correction: The slope term in (34) is the product of activation moduli and induced layer norms, although the final scalar norm may be arbitrary. → Multiply that product by the operator norm of the scalar coordinate map o.; reason: PDF p.17 permits arbitrary final-layer norms, while p.41 estimates the absolute scalar output; the one-layer optimized counterexample in DISPROOF.md falsifies the printed coefficient. No source cases are excluded.
--   - encoding: Finite Euclidean coordinates, ordinary expectations and mathematical optimization notation. → Coordinate-free normed spaces or real Hilbert spaces, extended nonnegative integrals and guarded extended extrema, with all sample and piece ranges explicit.; reason: These representations preserve the source domain, arbitrary norms, exact constants, and infinite values; nonnegative loss and measurable probability spaces are the standing conventions.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p. 18, Theorem 3.30; Appendix A proof

import Mathlib
import Definitions.Def_RegMT_Classif_Supplement_Neural

open scoped ENNReal

namespace RegMT.Classif.Supplement

/-- Corrected for arbitrary final-layer scalar norm; see DISPROOF.md. -/
theorem theorem_3_30 {M : ℕ} (hM : 0 < M) (A : Layers M)
    [MeasurableSpace (A.Space 0)] [BorelSpace (A.Space 0)] {N : ℕ} (hN : 0 < N)
    (X : Set (A.Space 0)) (hX : MeasurableSet X) (x : Fin N → A.Space 0) (hx : ∀ i, x i ∈ X)
    (L : ℝ → ℝ) (hconvex : ConvexOn ℝ Set.univ L) (hnonneg : ∀ t, 0 ≤ L t)
    (hlip : ∃ K, LipschitzWith K L) (κ : ℝ≥0∞) (hκ : 0 < κ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∀ (Y : Set ℝ), MeasurableSet Y → ∀ y : Fin N → ℝ, (∀ i, y i ∈ Y) →
      (⨅ W : Weights A, neuralRegRisk A X Y x y L κ ρ W) ≤
        ⨅ W : Weights A, neuralRegBound A x y L κ ρ W) ∧
    (∀ y : Fin N → Bool,
      (⨅ W : Weights A, neuralClassRisk A X x y L κ ρ W) ≤
        ⨅ W : Weights A, neuralClassBound A X x y L κ ρ W) := by sorry

end RegMT.Classif.Supplement
