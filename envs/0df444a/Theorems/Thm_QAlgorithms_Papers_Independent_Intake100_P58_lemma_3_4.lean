-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P58_lemma_3_4
-- name    : QAlgorithms.Papers.Independent.Intake100.P58.lemma_3_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:07:40.051355+00:00
-- url     : https://prove2.me/theorems/2b15f2b6-df6f-4911-8097-cf400095c6d3
-- title:
--   Lemma 3.4: full relations and the specified rank-k module
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
--   For $0\le m<k$, all of the following identities hold, with rightmost operators acting first:
--   $$
--   \begin{gathered}
--   \sum_{l=0}^kq_l\bar Y^l=0,\quad q_k=-1,\qquad
--   \bar X\bar W=\bar W\bar X=\operatorname{id},\\
--   \bar X\bar E=\bar E\bar X=\lambda\bar E,\qquad
--   \bar Y\bar X\bar Y\bar X=\bar X\bar Y\bar X\bar Y,\\
--   \bar E\bar Y^m\bar E=A_m\bar E,\qquad
--   \bar E\bar Y\bar X\bar Y=\bar Y\bar X\bar Y\bar E=\lambda^{-1}\bar E.
--   \end{gathered}
--   $$
--
--   Furthermore there exists a unital $R$-algebra homomorphism
--   $$
--   \rho:B\longrightarrow\operatorname{End}_R(V),\qquad
--   \rho(Y)=\bar Y,\quad\rho(X)=\bar X,\quad\rho(X^{-1})=\bar W,\quad\rho(e)=\bar E.
--   $$
--   Thus the specified free rank-$k$ module carries the stated $B$-action; the action is obtained as a conclusion, not assumed.
-- source:
--   The cyclotomic BMW algebra associated with the two string type B braid group, arXiv:math/0611518v3, PDF p. 10, Lemma 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P58

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intake100.P58

open Accepted

variable {R : Type*} [CommRing R] {k : ℕ}

/-- Lemma 3.4, PDF pp.10--11: all six identity groups and existence of
the specified compatible unital algebra action, including X inverse. -/
theorem lemma_3_4 (P : NonsplitParameters R k) (hdelta : RegularDelta P) (hadm : TwoStrandAdmissible P) :
    OperatorRelations P (Yv P) (Xv P) (Wv P) (Ev P) ∧
    ∃ rho : TwoStrandBMW P →ₐ[R] Module.End R (CompanionModule P), CompatibleV P rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P58

end
