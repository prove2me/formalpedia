-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_quotientDomain_regularity
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.quotientDomain_regularity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:11:10.43171+00:00
-- url     : https://prove2.me/theorems/7ac6b058-3eec-46a3-b75a-adc8f19376d6
-- title:
--   Descending regularity through a quotient domain
-- statement:
--   Let $K$ be a Hausdorff nondiscrete topological field, $E,F$ be Hausdorff topological $K$-vector spaces, and $N\subseteq E$ be a closed vector subspace. Give $E/N$ the quotient topology and let $q:E\to E/N$ be the canonical quotient map. For open $U\subseteq E$ and $U_1\subseteq E/N$ satisfying $q(U)=U_1$, a map $f_1:U_1\to F$, and $r\in\mathbb N_0\cup\{\infty\}$,
--   $$f_1\in C^r(U_1,F)\quad\Longleftrightarrow\quad f_1\circ q|_U\in C^r(U,F).$$
--
--   No complement of $N$ or continuous section of $q$ is required.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 49, Lemma 10.4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

section TopologicalFieldResults

variable {K : Type} [Field K] [TopologicalSpace K]

variable [hKTop : IsTopologicalDivisionRing K] [hKT2 : T2Space K]

variable (hNonDiscrete : ¬ DiscreteTopology K)

variable {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]

variable [hETop : IsTopologicalAddGroup E] [hESmul : ContinuousSMul K E] [hET2 : T2Space E]

variable {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F]

variable [hFTop : IsTopologicalAddGroup F] [hFSmul : ContinuousSMul K F] [hFT2 : T2Space F]

include hKTop hKT2 hNonDiscrete hETop hESmul hET2 hFTop hFSmul hFT2

/-- Lemma 10.4, PDF pp. 49--50: the actual quotient topology and exact
image condition q(U)=V; no continuous section or complement is assumed. -/
theorem quotientDomain_regularity
    (N : Submodule K E) (hN : IsClosed (N : Set E))
    (U : Set E) (hU : IsOpen U) (V : Set (E ⧸ N)) (hV : IsOpen V)
    (hImage : (fun x : E => (N.mkQ x : E ⧸ N)) '' U = V)
    (f : (E ⧸ N) → F) (r : WithTop ℕ) :
    fieldCr (K := K) r V f ↔
      fieldCr (K := K) r U (fun x => f (N.mkQ x)) := by sorry

end TopologicalFieldResults

end QAlgorithms.Papers.Independent.Renew46.P32
