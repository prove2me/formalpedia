-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P04_exponential_naturality
-- name    : QAlgorithms.Papers.Independent.Intake100.P04.exponential_naturality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:42:57.174581+00:00
-- url     : https://prove2.me/theorems/65b9777e-f9f2-4f80-a786-af80e5bc3c00
-- title:
--   Naturality of smooth Lie group exponential functions
-- statement:
--   Let $G$ and $H$ be Hausdorff Lie groups modelled on real Hausdorff locally convex spaces, with smooth exponential functions $\exp_G$ and $\exp_H$ defined by the global left-invariant initial-value problems. Let $\alpha:G\to H$ be a smooth group homomorphism, and let $d\alpha_e:T_eG\to T_eH$ be its differential at the identity. Then
--
--   $$
--   \alpha(\exp_G x)=\exp_H(d\alpha_e x)\qquad(x\in T_eG).
--   $$
--
--   Thus the exponential functions are natural under Lie group morphisms. Local invertibility of either exponential, normability and completeness of the modelling spaces are not required.
--
--   **Formalization Note** Identity charts identify the two tangent spaces with their models. The differential is computed as the limit of the actual coordinate difference quotients of $\alpha$, with chart centres subtracted.
-- source:
--   Lie Group Structures on Symmetry Groups of Principal Bundles, arXiv:math/0612522v1, PDF p. 24, Lemma A.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P04

namespace QAlgorithms.Papers.Independent.Intake100.P04

open Set Filter Topology

open QAlgorithms.Papers.Independent.Next46.P35

open QAlgorithms.Papers.Independent.Bridge50.P08 (HasLeftVelocity identityDifferential)

open QAlgorithms.Papers.Independent.Gap48.P05 (ExponentialLieData)

universe u v w z

attribute [local instance] QAlgorithms.Papers.Independent.Intake100.P04.productCharts

section Exponentials

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

variable {G : Type v} [Group G] [TopologicalSpace G] [ChartedSpace E G]

variable {F : Type w} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

variable {H : Type z} [Group H] [TopologicalSpace H] [ChartedSpace F H]

/-- Lemma A.6, PDF p. 24: every smooth group morphism intertwines
the given smooth exponential functions and its actual identity differential.
Both groups are Hausdorff locally convex Lie groups; neither normability,
completeness nor local exponentiality is assumed. The imported exponential
data encode smooth one-parameter groups with the prescribed identity tangent:
gamma_x(t) = exp(t x) solves A.5, and conversely its global ODE solutions
yield these one-parameter groups. The imported differential is specialized
to homomorphisms, so alpha(1) = 1 fixes its target chart centre. -/
theorem exponential_naturality
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E] [T2Space G]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F] [T2Space F] [T2Space H]
    (LG : ExponentialLieData E G)
    (LH : ExponentialLieData F H)
    (alpha : G →* H)
    (hSmooth : DirectionalManifoldSmooth (E := E) (F := F) alpha) :
    ∀ x : E, alpha (LG.exponential x) =
      LH.exponential (identityDifferential (E := E) (F := F) alpha x) := by sorry

end Exponentials

end QAlgorithms.Papers.Independent.Intake100.P04
