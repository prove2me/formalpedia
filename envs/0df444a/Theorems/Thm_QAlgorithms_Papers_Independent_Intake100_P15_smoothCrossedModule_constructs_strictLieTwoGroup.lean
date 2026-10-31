-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P15_smoothCrossedModule_constructs_strictLieTwoGroup
-- name    : QAlgorithms.Papers.Independent.Intake100.P15.smoothCrossedModule_constructs_strictLieTwoGroup
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:17:18.863584+00:00
-- url     : https://prove2.me/theorems/5a430ec5-1b2c-40ce-82f2-0417cd6a6663
-- title:
--   Appendix A.2: smooth crossed modules construct strict Lie 2-groups
-- statement:
--   Let $(G,H,t,\alpha)$ be a smooth crossed module of finite-dimensional real Lie groups: $t:H\to G$ is a smooth homomorphism and $\alpha:G\times H\to H$ is a smooth left action by group automorphisms satisfying both Peiffer identities. No connectedness is required. The following computed structure is a strict Lie 2-group. Its objects are $G$, its arrows are $G\times H$, and its source, target, identity and vertical composition are
--
--   $$
--   s(g,h)=g,\qquad r(g,h)=t(h)g,\qquad \operatorname{id}_g=(g,1),\qquad
--   (g',h')\mathbin{\bullet}(g,h)=(g,h'h)\quad(g'=t(h)g).
--   $$
--
--   The object tensor product is multiplication in $G$; the arrow tensor product and inverse functor are
--
--   $$
--   (g_2,h_2)\boxtimes(g_1,h_1)=(g_2g_1,h_2\alpha(g_2,h_1)),\qquad
--    i(g,h)=(g^{-1},\alpha(g^{-1},h^{-1})).
--   $$
--
--   All structure maps are smooth, the source and target are surjective submersions, the identity map is a smooth embedding, and the groupoid, strict tensor, unit, interchange and inverse-functor laws all hold. In particular $a\boxtimes i(a)=i(a)\boxtimes a=(1,1)$. The categorical inverse of $(g,h)$ is $(t(h)g,h^{-1})$.
--
--   This is the full forward construction in Appendix A.2, supplying both compositions in the associated one-object Lie 2-groupoid. It makes no assertion about the converse classification.
--
--   **Formalization Note** The complete structure laws are expanded in the predicate `IsConstructedStrictLieTwoGroup` on these computed maps. Composition smoothness is expressed through its displayed smooth extension on the ambient arrow product; the categorical laws use only composable arrows. In finite dimension, the explicit surjectivity of the differentials gives submersion, and the topological embedding together with injective differentials gives smooth embedding.
-- source:
--   Smooth Functors vs. Differential Forms, arXiv:0802.0663v4, PDF p. 66, Appendix A.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P15

namespace QAlgorithms.Papers.Independent.Intake100.P15

open scoped Manifold ContDiff

universe u v w z

section SmoothCrossedModules

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {F : Type z} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {G : Type u} [Group G] [TopologicalSpace G] [ChartedSpace E G]

variable {H : Type v} [Group H] [TopologicalSpace H] [ChartedSpace F H]

/-- Appendix A.2, PDF pp. 66–68: the explicit smooth crossed-module
construction gives a strict Lie 2-group with all unit/composition and inverse
laws. The computed maps are those of (A.3)–(A.7), not freely supplied maps.
Finite-dimensional, Hausdorff, second-countable manifolds without boundary
are assumed; no connectedness is needed. -/
theorem smoothCrossedModule_constructs_strictLieTwoGroup
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [T2Space G] [SecondCountableTopology G] [IsManifold (𝓘(ℝ, E)) ∞ G]
    [T2Space H] [SecondCountableTopology H] [IsManifold (𝓘(ℝ, F)) ∞ H]
    [LieGroup (𝓘(ℝ, E)) ∞ G] [LieGroup (𝓘(ℝ, F)) ∞ H]
    (t : H → G) (alpha : G × H → H)
    (hCrossed : IsSmoothCrossedModule (E := E) (F := F) t alpha) :
    IsConstructedStrictLieTwoGroup (E := E) (F := F) t alpha := by sorry

end SmoothCrossedModules

end QAlgorithms.Papers.Independent.Intake100.P15
