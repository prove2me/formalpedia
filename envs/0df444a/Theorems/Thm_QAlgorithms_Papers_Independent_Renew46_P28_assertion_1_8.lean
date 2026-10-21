-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P28_assertion_1_8
-- name    : QAlgorithms.Papers.Independent.Renew46.P28.assertion_1_8
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T02:55:15.058771+00:00
-- url     : https://prove2.me/theorems/21921257-befa-45da-a8d3-fb8fee8c1280
-- title:
--   The ordinary difference quotient and its continuous extension
-- statement:
--   Let $\mathbb K$ be a Hausdorff nondiscrete topological field, $E,F$ Hausdorff topological $\mathbb K$-vector spaces, $U\subseteq E$ open, and $f:U\to F$ arbitrary. Write $U^{[1]}=\{(x,y,t):x,x+ty\in U\}$ and $U^{]1[}=\{(x,y,t)\in U^{[1]}:t\ne0\}$. On this latter domain put $f^{]1[}(x,y,t)=t^{-1}(f(x+ty)-f(x))$. Then
--
--   $$
--   f\in C^1_{\mathbb K}\ \Longleftrightarrow\ f\text{ is continuous and }f^{]1[}\text{ has a continuous extension to }U^{[1]}.
--   $$
--
--   The set $U^{]1[}$ is open and dense in $U^{[1]}$, and $U^{[1]}=U^{]1[}\sqcup(U\times E\times\{0\})$. For every $k\in\mathbb N_0\cup\{\infty\}$, if $f$ is $C^k_{\mathbb K}$, then $f^{]1[}$ is $C^k_{\mathbb K}$ as well.
--
--   This identifies the ordinary quotient with the dense-domain data used by the extended-quotient calculus. All products have their product topologies; the empty domain is allowed.
-- source:
--   Lie groups over non-discrete topological fields, arXiv:math/0408008v1, PDF p. 14, Numbered assertion 1.8

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28

namespace QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w

/-- Assertion 1.8, PDF p.14: continuous extension characterization, openness and
density of the punctured domain, disjoint zero-slice decomposition, and preservation
of every finite or infinite regularity order by the ordinary quotient map. -/
theorem assertion_1_8
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (E : Type (max u v)) [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul K E]
    (F : Type w) [AddCommGroup F] [Module K F] [TopologicalSpace F]
    [T2Space F] [IsTopologicalAddGroup F] [ContinuousSMul K F]
    (U : Set E) (hU : IsOpen U) (f : U → F) :
    (bgnCr K F 1 U f ↔ Continuous f ∧
      ∃ g : differenceDomain K U → F,
        Continuous g ∧ extendsDifferenceQuotient K U f g) ∧
    IsOpen (puncturedDifferenceDomain K U) ∧
    Dense {z : differenceDomain K U | z.val.2.2 ≠ 0} ∧
    differenceDomain K U = puncturedDifferenceDomain K U ∪
      {z : E × E × K | z.1 ∈ U ∧ z.2.2 = 0} ∧
    Disjoint (puncturedDifferenceDomain K U)
      {z : E × E × K | z.1 ∈ U ∧ z.2.2 = 0} ∧
    (∀ k : WithTop ℕ, bgnCr K F k U f →
      bgnCr K F k (puncturedDifferenceDomain K U) (differenceQuotient K U f)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P28
