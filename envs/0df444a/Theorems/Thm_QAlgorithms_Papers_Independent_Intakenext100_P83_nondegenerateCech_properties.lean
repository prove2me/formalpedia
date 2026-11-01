-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P83_nondegenerateCech_properties
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P83.nondegenerateCech_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:10:35.16993+00:00
-- url     : https://prove2.me/theorems/7c47d21b-d779-4b8d-84b7-c786311b35f2
-- title:
--   Three properties of the nondegenerate ordered Čech complex
-- statement:
--   Let $\mathcal U=(U_\alpha)_{\alpha\in I}$ be an open cover of a topological space $X$, with nonempty members and a finite linearly ordered index set $I$. Define
--
--   $$
--   N_k=\coprod_{\alpha_0<\cdots<\alpha_k}U_{\alpha_0}\cap\cdots\cap U_{\alpha_k},\qquad
--   L^kN=\bigcup_{i=0}^{k+1}d_i(N_{k+1})\subseteq N_k.
--   $$
--
--   The coproducts carry their disjoint-union topologies, the intersections and $L^kN$ their subspace topologies, and $d_i$ deletes vertex $i$ while preserving the base point. Then:
--
--   1. There exists $K\in\mathbb N$ such that $N_k=\varnothing$ whenever $k>K$.
--   2. For every $k\ge0$, $0\le i<j\le k+1$, and $x,y\in N_{k+1}$ with $d_i(x)=d_j(y)$, there is $z\in N_{k+2}$ with $y=d_i(z)$ and $x=d_{j+1}(z)$.
--   3. For every $k\ge0$, the map $\coprod_{i=0}^{k+1}N_{k+1}\to L^kN$ given on summand $i$ by $d_i$ is a quotient map.
--
--   These statements describe the finite degree support, shared-face compatibility, and topology used in the subsequent shrinking argument. The space $L^kN$ is the union of face images, rather than a Reedy latching object.
-- source:
--   Two-Categorical Bundles and Their Classifying Spaces, arXiv:math/0612549v2, PDF p. 38, Lemma 6.19

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P83

open CategoryTheory

open scoped Simplicial

namespace QAlgorithms.Papers.Independent.Intakenext100.P83

universe u v

/-- Lemma 6.19, PDF p. 38, all three clauses. The shared-face conclusion uses
`j + 1`, represented by `j.succ`; `i.castSucc` represents the unchanged index.
There is no compactness, normality or CW assumption in this lemma. -/
theorem nondegenerateCech_properties
    {X : Type u} [TopologicalSpace X]
    {Index : Type v} [LinearOrder Index] [Fintype Index]
    (U : FiniteOrderedOpenCover X Index) :
    (∃ K : ℕ, ∀ k : ℕ, K < k → IsEmpty (NondegenerateCech U k)) ∧
    (∀ (k : ℕ) (i j : Fin (k + 2))
      (x y : NondegenerateCech U (k + 1)),
      i < j → cechFace U i x = cechFace U j y →
        ∃ z : NondegenerateCech U (k + 2),
          y = cechFace U i.castSucc z ∧ x = cechFace U j.succ z) ∧
    (∀ k : ℕ, Topology.IsQuotientMap (faceUnion U k)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P83
