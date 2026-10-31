-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P58_corollary_4_5
-- name    : QAlgorithms.Papers.Independent.Intake100.P58.corollary_4_5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:10:01.837173+00:00
-- url     : https://prove2.me/theorems/bd7e9cc0-b139-4db6-bb1c-2cb0d7972bb7
-- title:
--   Corollary 4.5: four equivalent characterizations
-- statement:
--   Let $k\ge1$ and let $R$ be a commutative unital ring. Choose units $q_0,q,\lambda\in R^\times$, coefficients $q_1,\ldots,q_{k-1}\in R$, and $A_0,\ldots,A_{k-1}\in R$. Put $\delta=q-q^{-1}$ and assume $\lambda-\lambda^{-1}=\delta(1-A_0)$. Let $B=B_2^k(R)$ be the unital associative algebra on invertible $Y,X$ and an element $e$, with relations (1)–(6) of Definition 2.1. In particular, $Y^k=\sum_{i=0}^{k-1}q_iY^i$, $X-X^{-1}=\delta(1-e)$, $XYXY=YXYX$, $Xe=eX=\lambda e$, $YXYe=eYXY=\lambda^{-1}e$, and $eY^me=A_me$ for $0\le m<k$.
--
--   Assume multiplication by $\delta$ on $R$ is injective (Assumption 2.2). Neither $A_0$ nor $\delta$ need be units, and the cyclotomic polynomial need not split.
--
--   Let $V=R^k$ with its standard basis $v_0,\ldots,v_{k-1}$. The operators $\bar Y,\bar X,\bar E$ are the specific maps (8)–(17): $\bar Yv_i=v_{i+1}$ for $i<k-1$, $\bar Yv_{k-1}=\sum_{i=0}^{k-1}q_iv_i$, $\bar Xv_0=\lambda v_0$, $\bar Xv_1=\lambda^{-1}\bar Y^{-1}v_0$ when $k>1$, $\bar Xv_i=\bar Y^{-1}\bar Xv_{i-1}-\delta v_{i-2}+\delta A_{i-1}\bar Y^{-1}v_0$ for $2\le i<k$, and $\bar Ev_i=A_iv_0$. Define $\bar W=\bar X-\delta\operatorname{id}_V+\delta\bar E$ and $v_s=\bar Y^sv_0$ for every integer $s$, using the explicit inverse (10)–(11).
--
--   The following four conditions are equivalent:
--
--   1. $B$ admits an $R$-basis indexed by $\{0,1,2\}\times\{0,\ldots,k-1\}^2$, so is free of the stated rank $3k^2$.
--   2. The family $(Y^ie)_{0\le i<k}$ is $R$-linearly independent in $B$.
--   3. $B$ has a free rank-$k$ module with the prescribed generator actions (8)–(9), (14)–(17); equivalently, on the fixed coordinate $V$, a unital representation sends $Y,X,e$ to $\bar Y,\bar X,\bar E$ (and hence $X^{-1}$ to $\bar W$).
--   4. The parameters are admissible as specified below.
--
--   In particular,
--   $$
--   (1)\Longleftrightarrow(2)\Longleftrightarrow(3)\Longleftrightarrow(4).
--   $$
--   Admissibility is a condition in this equivalence, not a hypothesis.
--
--   In condition (4), admissibility means the following equations of Definition 3.1: put $q_k=-1$, $z=\lceil k/2\rceil$ and $\epsilon=0$ for even $k$ and $1$ for odd $k$. The parameters satisfy $\beta=0$ and $h_l=0$ for $1\le l<k$, where
--   $$
--   \begin{aligned}
--   \beta&=q_0\lambda-q_0^{-1}\lambda^{-1}+(1-\epsilon)\delta,\\
--   h_l&=\lambda^{-1}(q_l+q_0^{-1}q_{k-l})+\delta\left(\sum_{r=1}^{k-l}q_{r+l}A_r-\sum_{i=\max(l+1,z)}^{\lfloor(l+k)/2\rfloor}q_{2i-l}+\sum_{i=\lceil l/2\rceil}^{\min(l,z-1)}q_{2i-l}\right).
--   \end{aligned}
--   $$
--
--   This characterizes exactly when the expected freeness holds under Assumption 2.2. Encoding condition (3) on $R^k$ transports any specified rank-$k$ basis to standard coordinates, and adds no restriction on the module.
--
--   **Formalization Note** The tensor summands use their canonical coordinates, indexed by $\{0,1,2\}\times\{0,\ldots,k-1\}^2$. Finite direct sums use the equivalent finite product. Rank is expressed by an indexed basis, without requiring $R$ to be nonzero.
-- source:
--   The cyclotomic BMW algebra associated with the two string type B braid group, arXiv:math/0611518v3, PDF p. 18, Corollary 4.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P58

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intake100.P58

open Accepted

variable {R : Type*} [CommRing R] {k : ℕ}

/-- Corollary 4.5, PDF pp.18--19. Admissibility is one of the four
EQUIVALENT conclusions, not a hypothesis. Rank means existence of a basis
of the specified finite cardinality, including for the zero ring. -/
theorem corollary_4_5 (P : NonsplitParameters R k) (hdelta : RegularDelta P) :
    let rankCondition := Nonempty (Module.Basis (XiIndex k) R (TwoStrandBMW P))
    let independentCondition := LinearIndependent R (fun i : Fin k => y P ^ i.val * e P)
    let moduleCondition := ∃ rho : TwoStrandBMW P →ₐ[R] Module.End R (CompanionModule P), CompatibleV P rho
    (rankCondition ↔ independentCondition) ∧
      (independentCondition ↔ moduleCondition) ∧
      (moduleCondition ↔ TwoStrandAdmissible P) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P58

end
