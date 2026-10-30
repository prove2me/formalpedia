-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P08_exponential_naturality
-- name    : QAlgorithms.Papers.Independent.Bridge50.P08.exponential_naturality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:17:35.276993+00:00
-- url     : https://prove2.me/theorems/3d1102e2-c987-4de4-a89d-c7981e14daf2
-- title:
--   Exponential naturality for locally convex Lie groups
-- statement:
--   Let $G$ and $K$ be Hausdorff Lie groups modelled on arbitrary Hausdorff locally convex real vector spaces, with smooth chart changes in the jointly continuous directional calculus. Suppose their smooth exponential functions $\exp_G$ and $\exp_K$ are defined by the global left invariant initial-value problem. For every smooth group homomorphism $a:G\to K$ and every $x\in T_1G$,
--
--   $$a(\exp_G(x))=\exp_K(T_1a(x)).$$
--
--   This compatibility transfers one-parameter evolutions along smooth homomorphisms. No local exponentiality, regularity, completeness, or finite dimension is assumed.
--
--   **Formalization Note** Identity charts identify the tangent spaces with their locally convex models. The induced differential is computed as the limit of the actual coordinate difference quotients of the homomorphism, with both chart centres retained.
-- source:
--   Principal 2-bundles and their gauge 2-groups, arXiv:0803.3692v4, PDF p. 36, Lemma A.4: exponential naturality for smooth homomorphisms

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P08

namespace QAlgorithms.Papers.Independent.Bridge50.P08

open Set Filter Topology

open QAlgorithms.Papers.Independent.Renew46.P18

open QAlgorithms.Papers.Independent.Claimed50.P22

open QAlgorithms.Papers.Independent.Next46.P35

universe u v w z

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P08.productCharts

/-- Lemma A.4, PDF pp. 35–36: exponential naturality for every smooth
homomorphism. Tangents are expressed in the actual identity charts;
the exponential functions solve A.3's global ODE. Local exponentiality,
regularity, finite dimension and completeness are not hypotheses. -/
theorem exponential_naturality
    {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F] [T2Space F]
    {G : Type w} {K : Type z}
    [Group G] [TopologicalSpace G] [T2Space G] [ChartedSpace E G]
    [Group K] [TopologicalSpace K] [T2Space K] [ChartedSpace F K]
    (hG : IsDirectionalLieGroup (E := E) (G := G))
    (hK : IsDirectionalLieGroup (E := F) (G := K))
    (expG : E → G) (expK : F → K)
    (hExpG : IsExponentialFunction expG)
    (hExpK : IsExponentialFunction expK)
    (alpha : G →* K)
    (hAlpha : DirectionalManifoldSmooth (E := E) (F := F) alpha) :
    ∀ x : E, alpha (expG x) = expK (identityDifferential alpha x) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P08
