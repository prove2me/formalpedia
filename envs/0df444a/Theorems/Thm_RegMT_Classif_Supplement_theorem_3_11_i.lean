-- Prove2me | Theorems.Thm_RegMT_Classif_Supplement_theorem_3_11_i
-- name    : RegMT.Classif.Supplement.theorem_3_11_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:31:45.963114+00:00
-- url     : https://prove2.me/theorems/d0d7b72a-e529-43ba-ba96-9261545230a7
-- title:
--   Theorem 3.11(i) — piecewise affine classification
-- statement:
--   Let $L(t)=\max_{j\le J}(a_jt+b_j)$ be nonnegative, $N,J\ge1$, $X$ a closed convex feature support containing the training inputs, and $\kappa>0$. Use any feature norm, binary labels, and $\rho\ge0$. For every $w$, the robust expected loss equals the value of (17), with both label branches:
--   $$S_X(a_j\hat y_iw-p^+_{ij})+b_j+p^+_{ij}(\hat x_i)\le s_i,$$
--   $$S_X(-a_j\hat y_iw-p^-_{ij})+b_j+p^-_{ij}(\hat x_i)-\kappa\lambda\le s_i,\qquad\|p^+_{ij}\|_*,\|p^-_{ij}\|_*\le\lambda.$$
--   The program minimizes $\lambda\rho+N^{-1}\sum_i s_i$. Its value equals the inner worst-case value for every $w$, and the two infima over $w$ also agree. This is the support-sensitive companion of the published full-space goal.
--
--   Differences from the source:
--   - encoding: Finite Euclidean coordinates, ordinary expectations and mathematical optimization notation. → Coordinate-free normed spaces or real Hilbert spaces, extended nonnegative integrals and guarded extended extrema, with all sample and piece ranges explicit.; reason: These representations preserve the source domain, arbitrary norms, exact constants, and infinite values; nonnegative loss and measurable probability spaces are the standing conventions.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p. 11, Theorem 3.11(i); Appendix A proof

import Mathlib
import Definitions.Def_RegMT_Classif_Supplement_Linear

open scoped ENNReal

namespace RegMT.Classif.Supplement

theorem theorem_3_11_i {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {N J : ℕ}
    (hN : 0 < N) (hJ : 0 < J) (X : Set V) (hclosed : IsClosed X) (hconvex : Convex ℝ X)
    (x : Fin N → V) (hx : ∀ i, x i ∈ X) (y : Fin N → Bool) (a b : Fin J → ℝ)
    (L : ℝ → ℝ) (hL : Piecewise a b L) (hnonneg : ∀ t, 0 ≤ L t)
    (κ ρ : ℝ) (hκ : 0 < κ) (hρ : 0 ≤ ρ) :
    (∀ w : V →L[ℝ] ℝ,
      (classRisk X x y κ ρ (fun ξ => L (DRLogReg.Reformulation.sgn ξ.2 * w ξ.1)) : EReal) =
        value17 X x y a b κ ρ w) ∧
    (⨅ w : V →L[ℝ] ℝ,
      (classRisk X x y κ ρ (fun ξ => L (DRLogReg.Reformulation.sgn ξ.2 * w ξ.1)) : EReal)) =
      ⨅ w : V →L[ℝ] ℝ, value17 X x y a b κ ρ w := by sorry

end RegMT.Classif.Supplement
