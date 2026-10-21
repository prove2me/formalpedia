-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P25_analyticFunctional_characterizations
-- name    : QAlgorithms.Papers.Independent.Next46.P25.analyticFunctional_characterizations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:58:10.275797+00:00
-- url     : https://prove2.me/theorems/73449416-4b80-451e-8880-27c16dda014d
-- title:
--   Analytic functionals: seminorm and Banach norm criteria
-- statement:
--   Let $\mathfrak g$ be a real Hausdorff locally convex Lie algebra with continuous bracket whose underlying space is Baire, and let $E$ be a real Banach space. Let $\beta:U(\mathfrak g)\to E$ be linear with continuous word maps $\beta_n$. For a continuous seminorm $p$, let $\|\beta_n^s\|_p\in[0,\infty]$ denote the supremum norm of the symmetrized word map on the product of $p$-unit balls. Then
--
--   $$
--   \beta\text{ is analytic}\quad\Longleftrightarrow\quad
--   \exists p\in\mathcal P(\mathfrak g):\ \sum_{n=0}^{\infty}\frac{\|\beta_n^s\|_p}{n!}<\infty.
--   $$
--
--   If $\mathfrak g$ is Banach with a compatible submultiplicative norm $p$, these are also equivalent to the existence of $t>0$ such that $\sum_{n\ge0}\|\beta_n^s\|_p t^n/n!<\infty$. The zeroth word is $1$ and $0!=1$. Analyticity here means convergence of the vector exponential series on a zero-neighborhood.
--
--   This gives both characterizations in Proposition 3.4. The Banach norm is represented by a definite continuous seminorm inducing the given topology, with completeness in the compatible additive uniformity.
-- source:
--   On Analytic Vectors for Unitary Representations of Infinite Dimensional Lie Groups, arXiv:1002.4792v2, PDF p. 9, Proposition 3.4

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

/-- Proposition 3.4, PDF pp.9--10: both seminorm and Banach-norm
    characterizations of analyticity, including degree zero. -/
theorem analyticFunctional_characterizations [CompleteSpace E] [BaireSpace g]
    (hBracket : Continuous (fun xy : g × g => ⁅xy.1, xy.2⁆))
    (beta : UniversalEnvelopingAlgebra ℝ g →ₗ[ℝ] E)
    (hContinuous : ContinuousFunctional beta) :
    (AnalyticFunctional beta ↔
      ∃ p : Seminorm ℝ g, Continuous p ∧ FiniteSymmetricSeries beta p 1) ∧
    (∀ p : Seminorm ℝ g, CompatibleBanachLieNorm p →
      (AnalyticFunctional beta ↔
        ∃ t : ℝ, 0 < t ∧ FiniteSymmetricSeries beta p t)) := by sorry

end Functionals

end QAlgorithms.Papers.Independent.Next46.P25

end
