-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P58_corollary_4_4
-- name    : QAlgorithms.Papers.Independent.Intake100.P58.corollary_4_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:09:28.567235+00:00
-- url     : https://prove2.me/theorems/fd4e661a-d2ce-441d-8b69-1263402286ed
-- title:
--   Corollary 4.4: ideal basis and exact column-module direct sum
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
--   Let $I=BeB$, and put $C_j=\operatorname{span}_R\{Y^ieY^j:0\le i<k\}$ for each $0\le j<k$. The ideal has the specified basis and column decomposition:
--   $$
--   I=\bigoplus_{j=0}^{k-1}C_j,\qquad
--   \{Y^ieY^j:0\le i,j<k\}\text{ is an }R\text{-basis of }I.
--   $$
--   There is the compatible representation of Lemma 3.4 on $V$, and each actual column is a left $B$-module isomorphic to $V$ by
--   $$
--   f_j:V\overset{\sim}{\longrightarrow}C_j,\qquad v_i\longmapsto Y^ieY^j.
--   $$
--   The sum map $(z_j)_j\mapsto\sum_jf_j(z_j)$ is a $B$-module isomorphism from the direct sum of $k$ copies of $V$ onto $I$. Thus both the summands and the identifications are the ones named in the source, rather than an unrelated abstract decomposition.
--
--   **Formalization Note** The tensor summands use their canonical coordinates, indexed by $\{0,1,2\}\times\{0,\ldots,k-1\}^2$. Finite direct sums use the equivalent finite product. Rank is expressed by an indexed basis, without requiring $R$ to be nonzero.
-- source:
--   The cyclotomic BMW algebra associated with the two string type B braid group, arXiv:math/0611518v3, PDF p. 18, Corollary 4.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P58

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intake100.P58

open Accepted

variable {R : Type*} [CommRing R] {k : ℕ}

/-- Corollary 4.4, PDF p.18. The basis is the displayed ideal-basisWord family.
Each actual column is identified with CompanionModule by v_i -> Y^i e Y^j, and the
sum of these column maps is a bijective B-linear map from k copies of CompanionModule.
Finite products here are canonically the finite direct sum. -/
theorem corollary_4_4 (P : NonsplitParameters R k) (hdelta : RegularDelta P) (hadm : TwoStrandAdmissible P) :
    (∃ b : Module.Basis (Fin k × Fin k) R (twoSidedIdeal P),
      ∀ idx, (b idx : TwoStrandBMW P) = y P ^ idx.1.val * e P * y P ^ idx.2.val) ∧
    ∃ rho : TwoStrandBMW P →ₐ[R] Module.End R (CompanionModule P), CompatibleV P rho ∧
      ∃ f : ∀ j : Fin k, CompanionModule P ≃ₗ[R] column P j,
        (∀ (j i : Fin k), (f j (vNat P i.val) : TwoStrandBMW P) = y P ^ i.val * e P * y P ^ j.val) ∧
        (∀ j a z, (f j (rho a z) : TwoStrandBMW P) = a * (f j z : TwoStrandBMW P)) ∧
        ∃ F : (Fin k → CompanionModule P) ≃ₗ[R] twoSidedIdeal P,
          (∀ z, (F z : TwoStrandBMW P) = ∑ j : Fin k, (f j (z j) : TwoStrandBMW P)) ∧
          (∀ a z, (F (fun j => rho a (z j)) : TwoStrandBMW P) = a * (F z : TwoStrandBMW P)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P58

end
