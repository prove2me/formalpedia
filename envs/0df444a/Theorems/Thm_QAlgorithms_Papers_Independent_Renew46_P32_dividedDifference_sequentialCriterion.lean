-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_dividedDifference_sequentialCriterion
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.dividedDifference_sequentialCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:13:00.949556+00:00
-- url     : https://prove2.me/theorems/f921b35e-1472-446e-8034-bdfcba27dabc
-- title:
--   Sequential criterion for a Schikhof extension
-- statement:
--   Let $K$ be a Hausdorff metrizable nondiscrete topological field, $U\subseteq K$ be nonempty and open, $E$ be a Hausdorff topological $K$-vector space, and $n\ge1$. Let $f:U\to E$ be continuous. If $f^{>n<}(x_j)$ has a limit in $E$ for every sequence $(x_j)$ of pairwise-distinct tuples converging to a point of $U^{n+1}$, then
--   $$f\in C^n_{\mathrm{Sch}}(U,E)\quad\text{and}\quad f\in C^n_K(U,E).$$
--
--   Here the first condition means that the highest raw divided difference has a continuous extension to all tuples. The range $E$ need not be metrizable or complete.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 51, Lemma 10.7

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

section CurveExtensionResults

variable {K : Type} [Field K] [TopologicalSpace K]

variable [hKTop : IsTopologicalDivisionRing K] [hKT2 : T2Space K]

variable (hNonDiscrete : ¬ DiscreteTopology K)

variable {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]

variable [hETop : IsTopologicalAddGroup E] [hESmul : ContinuousSMul K E] [hET2 : T2Space E]

include hKTop hKT2 hNonDiscrete hETop hESmul hET2

/-- Lemma 10.7, PDF p. 51: metrizability is required only of K. The
limits lie in E; neither completeness nor a uniform rate is assumed. -/
theorem dividedDifference_sequentialCriterion
    [TopologicalSpace.MetrizableSpace K] (U : Set K) (hU : IsOpen U) (hUne : U.Nonempty)
    (f : K → E) (n : ℕ) (hn : 0 < n) (hf : ContinuousOn f U)
    (hLimits : ∀ (s : ℕ → (Fin (n + 1) → K)) (t : Fin (n + 1) → K),
      (∀ k, s k ∈ distinctTuples U n) → (∀ i, t i ∈ U) →
      Tendsto s atTop (𝓝 t) →
        ∃ y : E, Tendsto (fun k => rawCurve f n (s k)) atTop (𝓝 y)) :
    fieldSchikhof n U f ∧ fieldCk (K := K) n U f := by sorry

end CurveExtensionResults

end QAlgorithms.Papers.Independent.Renew46.P32
