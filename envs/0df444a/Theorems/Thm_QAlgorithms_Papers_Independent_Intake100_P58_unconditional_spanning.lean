-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P58_unconditional_spanning
-- name    : QAlgorithms.Papers.Independent.Intake100.P58.unconditional_spanning
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:10:25.963581+00:00
-- url     : https://prove2.me/theorems/20b62a40-fa24-4932-8d2a-e85056b82844
-- title:
--   Corollary 4.5 proof: arbitrary-ground-ring spanning
-- statement:
--   Let $k\ge1$ and let $R$ be a commutative unital ring. Choose units $q_0,q,\lambda\in R^\times$, coefficients $q_1,\ldots,q_{k-1}\in R$, and $A_0,\ldots,A_{k-1}\in R$. Put $\delta=q-q^{-1}$ and assume $\lambda-\lambda^{-1}=\delta(1-A_0)$. Let $B=B_2^k(R)$ be the unital associative algebra on invertible $Y,X$ and an element $e$, with relations (1)–(6) of Definition 2.1. In particular, $Y^k=\sum_{i=0}^{k-1}q_iY^i$, $X-X^{-1}=\delta(1-e)$, $XYXY=YXYX$, $Xe=eX=\lambda e$, $YXYe=eYXY=\lambda^{-1}e$, and $eY^me=A_me$ for $0\le m<k$.
--
--   No regularity or admissibility assumption is made. With $S$ the $R$-linear span of the three displayed word families,
--   $$
--   S=\operatorname{span}_R\{Y^ieY^j,\ Y^iXY^j,\ XY^iXY^j:0\le i,j<k\}=B.
--   $$
--   The span is invariant under left multiplication by $X,Y,e$ and contains $1$. More precisely, construct the coordinate operators (32)–(38) from the companion formulas (8)–(18), without supposing they define a representation. For the linear word map $\phi(v_{ij})=Y^ieY^j$, $\phi(u_{ij})=Y^iXY^j$, $\phi(w_{ij})=XY^iXY^j$, their multiplication formulas give
--   $$
--   \phi(\mathsf X\xi)=X\phi(\xi),\qquad
--   \phi(\mathsf Y\xi)=Y\phi(\xi),\qquad
--   \phi(\mathsf E\xi)=e\phi(\xi).
--   $$
--   Here $\Xi$ is the three-copy tensor coordinate space and $\xi\in\Xi$ is arbitrary. This is the source's arbitrary-ground-ring spanning assertion, with its generator stability and multiplication formulas; independence is not asserted.
--
--   **Formalization Note** The tensor summands use their canonical coordinates, indexed by $\{0,1,2\}\times\{0,\ldots,k-1\}^2$. Finite direct sums use the equivalent finite product. Rank is expressed by an indexed basis, without requiring $R$ to be nonzero.
-- source:
--   The cyclotomic BMW algebra associated with the two string type B braid group, arXiv:math/0611518v3, PDF p. 19, Corollary 4.5 proof

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P58

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intake100.P58

open Accepted

variable {R : Type*} [CommRing R] {k : ℕ}

/-- Corollary 4.5 proof, PDF p.19: spanning for ANY ground ring, with no
regularity or admissibility assumption. The generator-intertwining equalities
retain the multiplication formulas (32)--(38), and the span contains 1. -/
theorem unconditional_spanning (P : NonsplitParameters R k) :
    wordSpan P = ⊤ ∧
    (∀ z, wordMap P (Xxi P z) = x P * wordMap P z ∧
      wordMap P (Yxi P z) = y P * wordMap P z ∧
      wordMap P (Exi P z) = e P * wordMap P z) ∧
    (∀ a ∈ ({x P, y P, e P} : Set (TwoStrandBMW P)), ∀ z ∈ wordSpan P, a*z ∈ wordSpan P) ∧
    (1 : TwoStrandBMW P) ∈ wordSpan P := by sorry

end QAlgorithms.Papers.Independent.Intake100.P58

end
