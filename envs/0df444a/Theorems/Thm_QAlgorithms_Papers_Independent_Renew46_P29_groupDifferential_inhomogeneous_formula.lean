-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P29_groupDifferential_inhomogeneous_formula
-- name    : QAlgorithms.Papers.Independent.Renew46.P29.groupDifferential_inhomogeneous_formula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:01:31.148773+00:00
-- url     : https://prove2.me/theorems/4ee89b86-4548-463a-a879-0c90c1950d0f
-- title:
--   The inhomogeneous formula for the locally smooth group differential
-- statement:
--   Let $G$ be a Lie group modeled on a Hausdorff locally convex space over $\mathbb R$ or $\mathbb C$, and let $A$ be an abelian Lie group with a jointly smooth $G$-action by automorphisms. For $n\geq0$, let $f:G^n\to A$ be normalized and smooth on an identity neighborhood. Define $d_G=\Phi_{n+1}^{-1}d_{AS}\Phi_n$, where $\Phi_n f(g_0,\ldots,g_n)=g_0\cdot f(g_0^{-1}g_1,\ldots,g_{n-1}^{-1}g_n)$ and $d_{AS}$ is alternating deletion. Then $d_G f$ is again normalized and locally smooth, and
--
--   $$(d_G f)(g_0,\ldots,g_n)=g_0\cdot f(g_1,\ldots,g_n)+\sum_{j=1}^{n}(-1)^j f(g_0,\ldots,g_{j-1}g_j,\ldots,g_n)+(-1)^{n+1}f(g_0,\ldots,g_{n-1}).$$
--
--   In degree zero the formula reads $(d_G a)(g)=g\cdot a-a$. This identifies the differential transported from homogeneous cochains with the usual group-cochain formula.
-- source:
--   Abelian extensions of infinite-dimensional Lie groups, arXiv:math/0402303v1, PDF p. 61, Lemma B.3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P29

namespace QAlgorithms.Papers.Independent.Renew46.P29

open Set Filter Topology

universe u v

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P29.productManifoldCharts

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P29.cochainManifoldCharts

section GroupCochains

variable {G : Type*} [Group G] {A : Type*} [AddCommGroup A]

variable [DistribMulAction G A]

variable (K : Type*) [RCLike K]

variable {E F : Type*}

variable [AddCommGroup E] [Module K E] [TopologicalSpace E]

variable [AddCommGroup F] [Module K F] [TopologicalSpace F]

variable [TopologicalSpace G] [ChartedSpace E G]

variable [TopologicalSpace A] [ChartedSpace F A]

/-- Lemma B.3, PDF pp. 61--62: the differential defined through homogeneous
cochains has the displayed inhomogeneous formula and preserves normalized
local smoothness. All degrees, including zero, are retained. -/
theorem groupDifferential_inhomogeneous_formula
    (hG : DirectionalLieGroup K E G) (hA : DirectionalAddLieGroup K F A)
    (hAction : ManifoldSmoothOn K (E := (E × F)) (F := F) Set.univ
      (fun p : G × A => p.1 • p.2))
    (n : ℕ) (f : (Fin n → G) → A)
    (hf : LocallySmoothCochain K (E := E) (F := F) n f) :
    LocallySmoothCochain K (E := E) (F := F) (n + 1) (groupDifferential n f) ∧
      ∀ g, groupDifferential n f g = inhomogeneousDifferential n f g := by sorry

end GroupCochains

end QAlgorithms.Papers.Independent.Renew46.P29
