-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P58_lemma_3_2
-- name    : QAlgorithms.Papers.Independent.Intake100.P58.lemma_3_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:06:48.801356+00:00
-- url     : https://prove2.me/theorems/b71d0a27-21e9-43c7-9552-6b77c5e5fb78
-- title:
--   Lemma 3.2: triangular defect-image spans
-- statement:
--   Let $k\ge1$ and let $R$ be a commutative unital ring. Choose units $q_0,q,\lambda\in R^\times$, coefficients $q_1,\ldots,q_{k-1}\in R$, and $A_0,\ldots,A_{k-1}\in R$. Put $\delta=q-q^{-1}$ and assume $\lambda-\lambda^{-1}=\delta(1-A_0)$. Let $B=B_2^k(R)$ be the unital associative algebra on invertible $Y,X$ and an element $e$, with relations (1)–(6) of Definition 2.1. In particular, $Y^k=\sum_{i=0}^{k-1}q_iY^i$, $X-X^{-1}=\delta(1-e)$, $XYXY=YXYX$, $Xe=eX=\lambda e$, $YXYe=eYXY=\lambda^{-1}e$, and $eY^me=A_me$ for $0\le m<k$.
--
--   Assume multiplication by $\delta$ on $R$ is injective (Assumption 2.2). Neither $A_0$ nor $\delta$ need be units, and the cyclotomic polynomial need not split.
--
--   Also assume admissibility as in Definition 3.1: put $q_k=-1$, $z=\lceil k/2\rceil$ and $\epsilon=0$ for even $k$ and $1$ for odd $k$. The parameters satisfy $\beta=0$ and $h_l=0$ for $1\le l<k$, where
--   $$
--   \begin{aligned}
--   \beta&=q_0\lambda-q_0^{-1}\lambda^{-1}+(1-\epsilon)\delta,\\
--   h_l&=\lambda^{-1}(q_l+q_0^{-1}q_{k-l})+\delta\left(\sum_{r=1}^{k-l}q_{r+l}A_r-\sum_{i=\max(l+1,z)}^{\lfloor(l+k)/2\rfloor}q_{2i-l}+\sum_{i=\lceil l/2\rceil}^{\min(l,z-1)}q_{2i-l}\right).
--   \end{aligned}
--   $$
--
--   Let $V=R^k$ with its standard basis $v_0,\ldots,v_{k-1}$. The operators $\bar Y,\bar X,\bar E$ are the specific maps (8)–(17): $\bar Yv_i=v_{i+1}$ for $i<k-1$, $\bar Yv_{k-1}=\sum_{i=0}^{k-1}q_iv_i$, $\bar Xv_0=\lambda v_0$, $\bar Xv_1=\lambda^{-1}\bar Y^{-1}v_0$ when $k>1$, $\bar Xv_i=\bar Y^{-1}\bar Xv_{i-1}-\delta v_{i-2}+\delta A_{i-1}\bar Y^{-1}v_0$ for $2\le i<k$, and $\bar Ev_i=A_iv_0$. Define $\bar W=\bar X-\delta\operatorname{id}_V+\delta\bar E$ and $v_s=\bar Y^sv_0$ for every integer $s$, using the explicit inverse (10)–(11).
--
--   Set $N=\bar Y\bar X\bar Y\bar X-\operatorname{id}_V$. Then
--   $$
--   Nv_l\in\operatorname{span}_R\{v_i:1\le i<l\}\quad(l\ge1),\qquad
--   Nv_{-m}\in\operatorname{span}_R\{v_{-i}:0\le i<m\}\quad(m\ge0).
--   $$
--   Both index bounds concern arbitrary natural $l,m$, not just standard basis indices. In particular the first span is zero at $l=1$ and the second at $m=0$. These are the two triangular image bounds for the computed defect operator.
-- source:
--   The cyclotomic BMW algebra associated with the two string type B braid group, arXiv:math/0611518v3, PDF p. 9, Lemma 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P58

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intake100.P58

open Accepted

variable {R : Type*} [CommRing R] {k : ℕ}

/-- Lemma 3.2, PDF pp.9--10. N is the constructed defect. The positive
span is empty at l=1, and the negative span is empty at m=0. -/
theorem lemma_3_2 (P : NonsplitParameters R k) (hdelta : RegularDelta P) (hadm : TwoStrandAdmissible P) :
    (∀ l : ℕ, 1 ≤ l → Nv P (orbitVector P (l : ℤ)) ∈
      Submodule.span R {z | ∃ i : ℕ, 1 ≤ i ∧ i < l ∧ z = orbitVector P (i : ℤ)}) ∧
    (∀ m : ℕ, Nv P (orbitVector P (-(m : ℤ))) ∈
      Submodule.span R {z | ∃ i : ℕ, i < m ∧ z = orbitVector P (-(i : ℤ))}) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P58

end
