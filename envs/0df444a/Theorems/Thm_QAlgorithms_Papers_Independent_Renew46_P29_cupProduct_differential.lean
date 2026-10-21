-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P29_cupProduct_differential
-- name    : QAlgorithms.Papers.Independent.Renew46.P29.cupProduct_differential
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:02:20.549738+00:00
-- url     : https://prove2.me/theorems/4752c1d1-0daa-4c38-8ff9-124a168930f3
-- title:
--   Leibniz rule for the twisted group cup product
-- statement:
--   Let $G$ be a Lie group over $\mathbb R$ or $\mathbb C$ in the Hausdorff locally convex calculus, let $U,V,W$ be abelian Lie groups with jointly smooth $G$-actions, and let $m:U\times V\to W$ be continuous, biadditive and $G$-equivariant. For normalized locally smooth cochains $\alpha:G^p\to U$ and $\beta:G^q\to V$, with $p,q\geq0$, define
--
--   $$(\alpha\cup\beta)(g_1,\ldots,g_{p+q})=m\bigl(\alpha(g_1,\ldots,g_p),(g_1\cdots g_p)\cdot\beta(g_{p+1},\ldots,g_{p+q})\bigr).$$
--
--   The group-cochain differential satisfies
--
--   $$d_G(\alpha\cup\beta)=(d_G\alpha)\cup\beta+(-1)^p\alpha\cup(d_G\beta).$$
--
--   Empty products are identities, so both degree-zero cases are included. This rule is the cochain identity underlying products on locally smooth group cohomology.
-- source:
--   Abelian extensions of infinite-dimensional Lie groups, arXiv:math/0402303v1, PDF p. 78, Lemma F.2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P29

namespace QAlgorithms.Papers.Independent.Renew46.P29

open Set Filter Topology

universe u v

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P29.productManifoldCharts

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P29.cochainManifoldCharts

section CupProducts

variable {G U V W : Type*} [Group G]

variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]

variable [DistribMulAction G U] [DistribMulAction G V] [DistribMulAction G W]

variable (K : Type*) [RCLike K]

variable {E EU EV EW : Type*}

variable [AddCommGroup E] [Module K E] [TopologicalSpace E]

variable [AddCommGroup EU] [Module K EU] [TopologicalSpace EU]

variable [AddCommGroup EV] [Module K EV] [TopologicalSpace EV]

variable [AddCommGroup EW] [Module K EW] [TopologicalSpace EW]

variable [TopologicalSpace G] [ChartedSpace E G]

variable [TopologicalSpace U] [ChartedSpace EU U]

variable [TopologicalSpace V] [ChartedSpace EV V]

variable [TopologicalSpace W] [ChartedSpace EW W]

/-- Lemma F.2, PDF p. 78: Leibniz's rule for normalized locally smooth group
cochains with a continuous biadditive equivariant pairing. No vector-space
structure is imposed on the coefficient groups. The reindexing of the first
term merely identifies (p+1)+q with (p+q)+1. -/
theorem cupProduct_differential
    (hG : DirectionalLieGroup K E G)
    (hU : DirectionalAddLieGroup K EU U)
    (hV : DirectionalAddLieGroup K EV V)
    (hW : DirectionalAddLieGroup K EW W)
    (hActionU : ManifoldSmoothOn K (E := (E × EU)) (F := EU) Set.univ
      (fun p : G × U => p.1 • p.2))
    (hActionV : ManifoldSmoothOn K (E := (E × EV)) (F := EV) Set.univ
      (fun p : G × V => p.1 • p.2))
    (hActionW : ManifoldSmoothOn K (E := (E × EW)) (F := EW) Set.univ
      (fun p : G × W => p.1 • p.2))
    (m : U → V → W) (hContinuous : Continuous (fun a : U × V => m a.1 a.2))
    (hAddLeft : ∀ u v w, m (u + v) w = m u w + m v w)
    (hAddRight : ∀ u v w, m u (v + w) = m u v + m u w)
    (hEquivariant : ∀ (g : G) (u : U) (v : V), m (g • u) (g • v) = g • m u v)
    (p q : ℕ) (alpha : (Fin p → G) → U) (beta : (Fin q → G) → V)
    (hAlpha : LocallySmoothCochain K (E := E) (F := EU) p alpha)
    (hBeta : LocallySmoothCochain K (E := E) (F := EV) q beta) :
    ∀ g : Fin (p + q + 1) → G,
      groupDifferential (p + q) (cupProduct m p q alpha beta) g =
        cupProduct m (p + 1) q (groupDifferential p alpha) beta
          (fun i => g (Fin.cast (by omega) i)) +
        (-1 : ℤ) ^ p • cupProduct m p (q + 1) alpha (groupDifferential q beta) g := by sorry

end CupProducts

end QAlgorithms.Papers.Independent.Renew46.P29
