-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P58_lemma_4_1
-- name    : QAlgorithms.Papers.Independent.Intake100.P58.lemma_4_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:08:19.48316+00:00
-- url     : https://prove2.me/theorems/f9db03ca-1a6c-40d9-92ce-2232b8055789
-- title:
--   Lemma 4.1: the first-row shift
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
--   Let $\Xi=(V\otimes_R V)\oplus(V\otimes_R V)\oplus(V\otimes_R V)$, with the three copies of $v_i\otimes v_j$ denoted $v_{ij},u_{ij},w_{ij}$, respectively, also for integer orbit indices. On the first copy the left action acts on the first tensor factor, and the right action uses reversal on the second factor. Let $\mathsf X,\mathsf Y,\mathsf E,\mathsf W$ be exactly the operators (32)–(38), with $\mathsf W=\mathsf X-\delta\operatorname{id}_\Xi+\delta\mathsf E$. In particular $\mathsf Eu_{ij}=v_{00}Y^iXY^j$, $\mathsf Ew_{ij}=\lambda\mathsf Eu_{ij}$, $\mathsf Xu_{ij}=w_{ij}$, $\mathsf Xw_{ij}=u_{ij}+\delta w_{ij}-\delta\lambda\mathsf Eu_{ij}$, $\mathsf Yu_{ij}=u_{i+1,j}$, and $\mathsf Yw_{ij}=\mathsf Wu_{i,j+1}+\delta u_{1,i+j}-\delta\mathsf Y\mathsf Xv_{ij}$.
--
--   For every integer $i$,
--   $$
--   \mathsf Yw_{1i}=w_{1,i+1}.
--   $$
--   The first subscript $1$ is an integer orbit index, so this includes $k=1$. This first-row shift is a property of the constructed operator used in the full tensor representation.
--
--   **Formalization Note** The tensor summands use their canonical coordinates, indexed by $\{0,1,2\}\times\{0,\ldots,k-1\}^2$. Finite direct sums use the equivalent finite product. Rank is expressed by an indexed basis, without requiring $R$ to be nonzero.
-- source:
--   The cyclotomic BMW algebra associated with the two string type B braid group, arXiv:math/0611518v3, PDF p. 12, Lemma 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P58

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intake100.P58

open Accepted

variable {R : Type*} [CommRing R] {k : ℕ}

/-- Lemma 4.1, PDF pp.12--13. The first row is the INTEGER orbit index 1,
so the assertion includes k=1; it does not require a second standard basis row. -/
theorem lemma_4_1 (P : NonsplitParameters R k) (hdelta : RegularDelta P) (hadm : TwoStrandAdmissible P) :
    ∀ i : ℤ, Yxi P (tensorLabel P 2 1 i) = tensorLabel P 2 1 (i+1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P58

end
