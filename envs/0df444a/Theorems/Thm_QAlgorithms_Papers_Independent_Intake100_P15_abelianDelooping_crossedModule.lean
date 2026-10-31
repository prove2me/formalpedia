-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P15_abelianDelooping_crossedModule
-- name    : QAlgorithms.Papers.Independent.Intake100.P15.abelianDelooping_crossedModule
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:17:54.042017+00:00
-- url     : https://prove2.me/theorems/0746a739-b06f-406c-9b41-b5a1f0de8604
-- title:
--   Example A.8: abelian delooping crossed module
-- statement:
--   Let $A$ be any finite-dimensional abelian real Lie group and let $G=\{1\}$ be the trivial Lie group. The maps
--
--   $$t:A\longrightarrow G,\quad t(a)=1,\qquad
--   \alpha:G\times A\longrightarrow A,\quad\alpha(1,a)=a$$
--
--   form a smooth crossed module. Its associated Lie 2-group under the explicit crossed-module construction is denoted $BA$, and its one-object delooping is denoted $BBA$.
--
--   This specialization uses the commutativity of $A$ in the second Peiffer identity and does not choose any numerical normalization for the circle group.
--
--   **Formalization Note** The trivial group is represented by an arbitrary subsingleton Lie group $G$. All groups have finite-dimensional Hausdorff, second-countable manifold structures without boundary; there is no positive-dimensional or connectedness restriction on $A$.
-- source:
--   Smooth Functors vs. Differential Forms, arXiv:0802.0663v4, PDF p. 68, Example A.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P15

namespace QAlgorithms.Papers.Independent.Intake100.P15

open scoped Manifold ContDiff

universe u v w z

section SmoothCrossedModules

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {F : Type z} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {G : Type u} [Group G] [TopologicalSpace G] [ChartedSpace E G]

variable {H : Type v} [Group H] [TopologicalSpace H] [ChartedSpace F H]

/-- Example A.8, PDF p. 68: every abelian Lie group A gives the
abelian delooping crossed module. G is any representation of the trivial
Lie group, and alpha is exactly the projection to A. The associated Lie
2-group uses the construction above; no circle normalization is chosen. -/
theorem abelianDelooping_crossedModule
    {A : Type v} [CommGroup A] [TopologicalSpace A] [ChartedSpace F A]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [Subsingleton G] [T2Space G] [SecondCountableTopology G]
    [IsManifold (𝓘(ℝ, E)) ∞ G] [LieGroup (𝓘(ℝ, E)) ∞ G]
    [T2Space A] [SecondCountableTopology A]
    [IsManifold (𝓘(ℝ, F)) ∞ A] [LieGroup (𝓘(ℝ, F)) ∞ A] :
    IsSmoothCrossedModule (E := E) (F := F)
      (fun _ : A => (1 : G)) (fun p : G × A => p.2) ∧
    IsConstructedStrictLieTwoGroup (E := E) (F := F)
      (fun _ : A => (1 : G)) (fun p : G × A => p.2) := by sorry

end SmoothCrossedModules

end QAlgorithms.Papers.Independent.Intake100.P15
