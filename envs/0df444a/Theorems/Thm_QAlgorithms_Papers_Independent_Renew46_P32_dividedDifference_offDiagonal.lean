-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_dividedDifference_offDiagonal
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.dividedDifference_offDiagonal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:11:50.556725+00:00
-- url     : https://prove2.me/theorems/57a68912-6e51-452b-92e7-458a3d6999a6
-- title:
--   Extending divided differences away from the full diagonal
-- statement:
--   Let $K$ be a Hausdorff nondiscrete topological field, $E$ be a Hausdorff topological $K$-vector space, $U\subseteq K$ be nonempty and open, and $n\ge1$. Suppose $f:U\to E$ is $C^{n-1}$. Let $U^{>n<}$ denote the pairwise-distinct $(n+1)$-tuples and let $f^{>n<}$ be the recursively defined divided difference of Definition 6.3. There exists a continuous map
--   $$h:U^{n+1}\setminus\{(t,\ldots,t):t\in U\}\to E$$
--   whose restriction to $U^{>n<}$ equals $f^{>n<}$. This permits partially repeated coordinates; only the full diagonal is excluded.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 50, Lemma 10.5

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

/-- Lemma 10.5, PDF p. 50: extension off the FULL diagonal, allowing
partially repeated coordinates. -/
theorem dividedDifference_offDiagonal
    (U : Set K) (hU : IsOpen U) (hUne : U.Nonempty)
    (f : K → E) (n : ℕ) (hn : 0 < n)
    (hf : fieldCk (K := K) (n - 1) U f) :
    let V : Set (Fin (n + 1) → K) :=
      {t | (∀ i, t i ∈ U) ∧ ¬ ∃ a : K, ∀ i, t i = a}
    ∃ h : (Fin (n + 1) → K) → E,
      ContinuousOn h V ∧ Set.EqOn h (rawCurve f n) (distinctTuples U n) := by sorry

end CurveExtensionResults

end QAlgorithms.Papers.Independent.Renew46.P32
