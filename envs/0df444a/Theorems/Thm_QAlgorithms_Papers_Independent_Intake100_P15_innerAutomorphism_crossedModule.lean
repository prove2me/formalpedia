-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P15_innerAutomorphism_crossedModule
-- name    : QAlgorithms.Papers.Independent.Intake100.P15.innerAutomorphism_crossedModule
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:18:26.742255+00:00
-- url     : https://prove2.me/theorems/abb40aa4-51ec-4ec7-ad73-eb36f77cd635
-- title:
--   Example A.9: inner automorphism crossed module and unique 2-cells
-- statement:
--   Let $G$ be any finite-dimensional real Lie group. Taking $H=G$, $t=\operatorname{id}_G$ and $\alpha(g,h)=ghg^{-1}$ defines a smooth crossed module. Its associated Lie 2-group is denoted $EG$. The associated one-object Lie 2-groupoid has 1-morphisms $G$, composed by $g_2\circ g_1=g_2g_1$. For every pair $g,g'\in G$ there is exactly one 2-morphism $g\Rightarrow g'$, whose label is
--
--   $$h=g'g^{-1}.$$
--
--   This identifies the actual target-matching label used in the derivative 2-functor, including its noncommutative order. It does not assert a geometric realization as a universal bundle.
--
--   **Formalization Note** The unique 2-cell is expressed by its label together with the computed equation $t(h)g=g'$. The one-object delooping and its compositions are the conventions of Appendix A.2.
-- source:
--   Smooth Functors vs. Differential Forms, arXiv:0802.0663v4, PDF p. 68, Example A.9

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P15

namespace QAlgorithms.Papers.Independent.Intake100.P15

open scoped Manifold ContDiff

universe u v w z

section SmoothCrossedModules

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {F : Type z} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {G : Type u} [Group G] [TopologicalSpace G] [ChartedSpace E G]

variable {H : Type v} [Group H] [TopologicalSpace H] [ChartedSpace F H]

/-- Example A.9, PDF p. 68: the identity/conjugation crossed module
and its complete 2-cell classification. There is exactly one H-label from
g to gPrime, namely gPrime * g inverse, in this order. The unique object
and multiplication of 1-arrows are the delooping convention of Appendix A.2. -/
theorem innerAutomorphism_crossedModule
    [FiniteDimensional ℝ E]
    [T2Space G] [SecondCountableTopology G] [IsManifold (𝓘(ℝ, E)) ∞ G]
    [LieGroup (𝓘(ℝ, E)) ∞ G] :
    IsSmoothCrossedModule (E := E) (F := E)
      (id : G → G) (fun p : G × G => p.1 * p.2 * p.1⁻¹) ∧
    IsConstructedStrictLieTwoGroup (E := E) (F := E)
      (id : G → G) (fun p : G × G => p.1 * p.2 * p.1⁻¹) ∧
    ∀ g gPrime : G, ∃! h : G,
      crossedCoordinateTarget (id : G → G) (g, h) = gPrime ∧ h = gPrime * g⁻¹ := by sorry

end SmoothCrossedModules

end QAlgorithms.Papers.Independent.Intake100.P15
