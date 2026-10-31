-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P16_measurableFunctionSheaf_flasque
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P16.measurableFunctionSheaf_flasque
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:09:50.720735+00:00
-- url     : https://prove2.me/theorems/01fcf778-dd64-4ebd-af12-105f0e216eab
-- title:
--   Measurable coefficient sheaves are flasque
-- statement:
--   Let $G$ be a locally compact Hausdorff topological group, let $A$ be an abelian Lie group in the paper's Fréchet convention, and let $p\geq0$. Write $\mathcal M_A$ for the sheaf of germs of actual measurable $A$-valued functions on $G^p$, with the Borel structures induced by the given topologies. Sections are locally measurable functions, with no almost-everywhere identification. Then $\mathcal M_A$ is flasque: for every pair of open sets $U\subseteq V\subseteq G^p$, the restriction map is surjective,
--
--   $$
--   \operatorname{res}_{V,U}:\mathcal M_A(V)\twoheadrightarrow\mathcal M_A(U).
--   $$
--
--   This is the levelwise flasqueness input for the paper's computation of measurable cohomology by cochains.
--
--   **Formalization Note** The sheaf is constructed by localizing the predicate of Borel measurability. Flasqueness is tested on its underlying sheaf of sets, where epimorphisms are exactly surjections; this is the same restriction-surjectivity property for the abelian coefficient sheaf. Hausdorffness is the usual convention for locally compact groups. The supplied coefficient atlas, complete metrizable locally convex model, and global exponential are retained.
-- source:
--   Differentiable Cohomology of Gauge Groups, arXiv:math/0011069v1, PDF p. 11, Lemma 2.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P16

namespace QAlgorithms.Papers.Independent.Intakenext100.P16

open CategoryTheory TopologicalSpace Opposite Filter Topology

universe u v w

/-- Lemma 2.5, PDF p. 11: for a locally compact topological group G and
an abelian Lie coefficient group A, the sheaf of germs of measurable
A-valued functions on G^p is flasque, in every degree p including zero.
The underlying sheaf of sets is used: its restriction maps are surjective,
which is precisely the same flasqueness condition for this abelian sheaf.
The coefficient Lie data retain the paper's standing Fréchet convention. -/
theorem measurableFunctionSheaf_flasque
    (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (E : Type v) [AddCommGroup E] [Module ℝ E] [UniformSpace E]
    (A : Type w) [AddCommGroup A] [TopologicalSpace A] [ChartedSpace E A]
    (_coeff : FrechetAbelianLieData E A) (p : ℕ) :
    TopCat.Sheaf.IsFlasque
      (measurableFunctionSheaf (TopCat.of (Fin p → G)) A) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P16
