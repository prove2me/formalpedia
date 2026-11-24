-- Prove2me | Theorems.Thm_RegMT_Classif_Supplement_theorem_3_1_i
-- name    : RegMT.Classif.Supplement.theorem_3_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:30:26.570181+00:00
-- url     : https://prove2.me/theorems/0de0e917-aa89-4359-b61a-4e3a24c2b77f
-- title:
--   Theorem 3.1(i) — piecewise affine regression
-- statement:
--   Let $L(t)=\max_{j\le J}(a_jt+b_j)$ be a nonnegative loss, with $N,J\ge1$. Let the closed convex joint support $\Xi$ contain all training samples, and equip the input-output space with any norm. For every $\rho\ge0$ and every $w$, the worst-case expected residual loss equals the value of the full support-function program (5):
--   $$\sup_{Q\in B_\rho(\hat P_N)}\mathbb E_Q L(\langle w,x\rangle-y)=\inf_{\lambda,s,p}\left\{\lambda\rho+\frac1N\sum_i s_i:\ S_\Xi(a_jr_w-p_{ij})+b_j+p_{ij}(\hat\xi_i)\le s_i,\ \|p_{ij}\|_*\le\lambda\right\}.$$
--   Here $r_w(x,y)=\langle w,x\rangle-y$, and every constraint holds for all samples and pieces. Taking the infimum over $w$ gives equal optimization values as well. This retains arbitrary joint norms and support information, without requiring a conic representation or a Slater point.
--
--   Differences from the source:
--   - generalization: The support is the product X × Y of closed convex sets. → The joint support can be any closed convex subset of the arbitrary normed input-output space.; reason: The support-function argument uses only closedness and convexity; every source product support is included.
--   - encoding: Finite Euclidean coordinates, ordinary expectations and mathematical optimization notation. → Coordinate-free normed spaces or real Hilbert spaces, extended nonnegative integrals and guarded extended extrema, with all sample and piece ranges explicit.; reason: These representations preserve the source domain, arbitrary norms, exact constants, and infinite values; nonnegative loss and measurable probability spaces are the standing conventions.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p. 8, Theorem 3.1(i); Appendix A proof

import Mathlib
import Definitions.Def_RegMT_Classif_Supplement_Linear

open scoped ENNReal

namespace RegMT.Classif.Supplement

theorem theorem_3_1_i {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n N J : ℕ}
    (e : E ≃L[ℝ] (Fin n → ℝ) × ℝ) (hN : 0 < N) (hJ : 0 < J)
    (S : Set E) (hclosed : IsClosed S) (hconvex : Convex ℝ S)
    (z : Fin N → E) (hz : ∀ i, z i ∈ S) (a b : Fin J → ℝ)
    (L : ℝ → ℝ) (hL : Piecewise a b L) (hnonneg : ∀ t, 0 ≤ L t) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∀ w : Fin n → ℝ,
      (normRisk S z ρ (fun ξ => L (RegMT.Regress.pairing e w ξ)) : EReal) =
        value5 e S z a b ρ w) ∧
    (⨅ w : Fin n → ℝ, (normRisk S z ρ (fun ξ => L (RegMT.Regress.pairing e w ξ)) : EReal)) =
      ⨅ w : Fin n → ℝ, value5 e S z a b ρ w := by sorry

end RegMT.Classif.Supplement
