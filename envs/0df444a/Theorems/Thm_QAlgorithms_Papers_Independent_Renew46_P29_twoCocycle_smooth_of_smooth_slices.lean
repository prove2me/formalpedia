-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P29_twoCocycle_smooth_of_smooth_slices
-- name    : QAlgorithms.Papers.Independent.Renew46.P29.twoCocycle_smooth_of_smooth_slices
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:58:56.84364+00:00
-- url     : https://prove2.me/theorems/1c16c5f6-78c5-45ec-b578-257ce8cdb8c7
-- title:
--   Smooth slices of a locally smooth two-cocycle imply joint smoothness
-- statement:
--   Let $G$ be a connected Lie group in the Hausdorff locally convex calculus over $\mathbb R$ or $\mathbb C$, and let $A$ be an abelian Lie group with a jointly smooth $G$-action. Suppose $f:G\times G\to A$ is a normalized two-cocycle, smooth on an identity neighborhood, and that $x\mapsto f(g,x)$ is globally smooth for every $g\in G$. Then
--
--   $$f:G\times G\longrightarrow A\quad\text{is globally smooth}.$$
--
--   This criterion promotes local smoothness of a group cocycle to global smoothness without a completeness assumption. The slices here are ordinary second-variable slices.
-- source:
--   Abelian extensions of infinite-dimensional Lie groups, arXiv:math/0402303v1, PDF p. 32, Lemma VIII.1

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

/-- Lemma VIII.1, PDF p. 32: for a connected Lie group, a normalized locally
smooth two-cocycle whose second-variable slices are all globally smooth is
jointly globally smooth. Here f(g, -) is the slice, not II.5's conjugation
correction. No completeness or global smooth section is assumed. -/
theorem twoCocycle_smooth_of_smooth_slices
    [ConnectedSpace G]
    (hG : DirectionalLieGroup K E G) (hA : DirectionalAddLieGroup K F A)
    (hAction : ManifoldSmoothOn K (E := (E × F)) (F := F) Set.univ
      (fun p : G × A => p.1 • p.2))
    (f : G → G → A) (hf : NormalizedTwoCocycle f)
    (hLocal : LocallySmoothCochain K (E := E) (F := F) 2
      (fun g => f (g 0) (g 1)))
    (hSlices : ∀ g : G,
      ManifoldSmoothOn K (E := E) (F := F) Set.univ (fun x => f g x)) :
    ManifoldSmoothOn K (E := (E × E)) (F := F) Set.univ
      (fun p : G × G => f p.1 p.2) := by sorry

end GroupCochains

end QAlgorithms.Papers.Independent.Renew46.P29
