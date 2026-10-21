-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P25_fixedRadius_regular_invariance
-- name    : QAlgorithms.Papers.Independent.Next46.P25.fixedRadius_regular_invariance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:58:48.668412+00:00
-- url     : https://prove2.me/theorems/3465b2e0-8f39-40db-88c4-6e393e507d21
-- title:
--   Left and right regular actions preserve the fixed analytic radius
-- statement:
--   Let $\mathfrak g$ be a real Hausdorff locally convex Lie algebra with continuous bracket, let $E$ be Banach, and let $p$ be a continuous seminorm satisfying $p([x,y])\le p(x)p(y)$. For a continuous linear map $\beta:U(\mathfrak g)\to E$, let $R_{\beta,p}$ be the convergence radius of $\sum_{n\ge0}\|\beta_n^s\|_p t^n/n!$. For $r>0$, write $\mathcal A_{p,r}$ for the analytic maps with $R_{\beta,p}\ge r$, and write $\mathcal A_p$ for the analytic maps with positive $p$-radius. For $x\in\mathfrak g$, define $(L_x\beta)(D)=-\beta(xD)$ and $(R_x\beta)(D)=\beta(Dx)$. Then
--
--   $$
--   \beta\in\mathcal A_{p,r}\ \Longrightarrow\ L_x\beta,R_x\beta\in\mathcal A_{p,r},
--   \qquad
--   \beta\in\mathcal A_p\ \Longrightarrow\ L_x\beta,R_x\beta\in\mathcal A_p
--   \quad(x\in\mathfrak g).
--   $$
--
--   Thus the same seminorm and the same radius work for every Lie algebra element. Positive radius includes infinite radius, following the operative union in Definition 3.5.
-- source:
--   On Analytic Vectors for Unitary Representations of Infinite Dimensional Lie Groups, arXiv:1002.4792v2, PDF p. 10, Theorem 3.6

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P25

noncomputable section

open Set Filter Topology

open scoped Classical ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P25

universe u v w z

attribute [local instance 100] LieRing.ofAssociativeRing

section Functionals

variable {g : Type u} [LieRing g] [LieAlgebra ℝ g]

variable [gUniform : UniformSpace g] [gAdd : IsUniformAddGroup g] [gHaus : T2Space g]

variable [gScalar : ContinuousSMul ℝ g] [gLC : LocallyConvexSpace ℝ g]

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

include gAdd gHaus gScalar gLC

/-- Theorem 3.6, PDF pp.10--12: invariance of the SAME p,r subspace
    and, in particular, of the positive-p-radius space. -/
theorem fixedRadius_regular_invariance [CompleteSpace E]
    (hBracket : Continuous (fun xy : g × g => ⁅xy.1, xy.2⁆))
    (p : Seminorm ℝ g) (hp : Continuous p) (hSub : Submultiplicative p)
    (r : ℝ) (hr : 0 < r) :
    (∀ beta : UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E,
      AtRadius beta p r → ∀ x : g,
        AtRadius (leftRegular x beta) p r ∧ AtRadius (rightRegular x beta) p r) ∧
    (∀ beta : UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E,
      PAnalytic beta p → ∀ x : g,
        PAnalytic (leftRegular x beta) p ∧ PAnalytic (rightRegular x beta) p) := by sorry

end Functionals

end QAlgorithms.Papers.Independent.Next46.P25

end
