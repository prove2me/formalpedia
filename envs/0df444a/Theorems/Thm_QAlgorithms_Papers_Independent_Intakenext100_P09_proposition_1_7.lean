-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P09_proposition_1_7
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P09.proposition_1_7
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:12:18.514317+00:00
-- url     : https://prove2.me/theorems/f57c4b73-c206-4e7f-b002-38287c41e70d
-- title:
--   Proposition 1.7
-- statement:
--   Let $G$ be a topological group acting continuously on a topological space $X$, and let $V$ be a continuous abelian topological $G$-module. For an open cover $\mathcal U$, put $\mathcal U[n]=\bigcup_{W\in\mathcal U}W^{n+1}$, and let $A_{cr}^n(X,\mathcal U;V)$ be global functions continuous on this set. Let $A_{cg}^n$ be their union over all covers. With the homogeneous alternating differential, the canonical map
--
--   $$\underset{\mathcal U\text{ invariant open cover}}{\operatorname{colim}} A_{cr}^{\bullet}(X,\mathcal U;V)^G\longrightarrow A_{cg}^{\bullet}(X;V)^G$$
--
--   is a natural isomorphism of complexes. It is the identity on underlying global functions, and is bijective in every nonnegative degree. Refinement identifies the same global function, rather than identifying distinct functions with equal germs.
-- source:
--   A Spectral Sequence Connecting Continuous With Locally Continuous Group Cohomology, arXiv:1110.0994v1, PDF p. 3, Proposition 1.7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P09

universe u v w

/-- PDF pp. 3–4, Proposition 1.7: the canonical comparison from the cover
colimit of fixed cochains to fixed cochains in the cover colimit is degreewise
bijective. It acts identically on global functions and hence commutes with the
homogeneous differential and coefficient postcomposition. -/
theorem proposition_1_7 {G : Type w} {X : Type u} {V : Type v}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [DistribMulAction G V] [ContinuousSMul G V] :
    ∀ n : ℕ, Function.Bijective (coverComparison G (X := X) (V := V) n) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P09

end
