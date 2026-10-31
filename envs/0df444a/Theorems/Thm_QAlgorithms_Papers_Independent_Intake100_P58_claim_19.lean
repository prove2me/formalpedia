-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P58_claim_19
-- name    : QAlgorithms.Papers.Independent.Intake100.P58.claim_19
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:06:15.579448+00:00
-- url     : https://prove2.me/theorems/917b81fc-fd22-4295-81eb-2087db8eb9a1
-- title:
--   Section 3, explicit Claim (19): Wv formula
-- statement:
--   Let $k\ge1$ and let $R$ be a commutative unital ring. Choose units $q_0,q,\lambda\in R^\times$, coefficients $q_1,\ldots,q_{k-1}\in R$, and $A_0,\ldots,A_{k-1}\in R$. Put $\delta=q-q^{-1}$ and assume $\lambda-\lambda^{-1}=\delta(1-A_0)$. Let $B=B_2^k(R)$ be the unital associative algebra on invertible $Y,X$ and an element $e$, with relations (1)–(6) of Definition 2.1. In particular, $Y^k=\sum_{i=0}^{k-1}q_iY^i$, $X-X^{-1}=\delta(1-e)$, $XYXY=YXYX$, $Xe=eX=\lambda e$, $YXYe=eYXY=\lambda^{-1}e$, and $eY^me=A_me$ for $0\le m<k$.
--
--   Assume multiplication by $\delta$ on $R$ is injective (Assumption 2.2). Neither $A_0$ nor $\delta$ need be units, and the cyclotomic polynomial need not split.
--
--   Let $V=R^k$ with its standard basis $v_0,\ldots,v_{k-1}$. The operators $\bar Y,\bar X,\bar E$ are the specific maps (8)–(17): $\bar Yv_i=v_{i+1}$ for $i<k-1$, $\bar Yv_{k-1}=\sum_{i=0}^{k-1}q_iv_i$, $\bar Xv_0=\lambda v_0$, $\bar Xv_1=\lambda^{-1}\bar Y^{-1}v_0$ when $k>1$, $\bar Xv_i=\bar Y^{-1}\bar Xv_{i-1}-\delta v_{i-2}+\delta A_{i-1}\bar Y^{-1}v_0$ for $2\le i<k$, and $\bar Ev_i=A_iv_0$. Define $\bar W=\bar X-\delta\operatorname{id}_V+\delta\bar E$ and $v_s=\bar Y^sv_0$ for every integer $s$, using the explicit inverse (10)–(11).
--
--   For each $0\le l<k$,
--   $$
--   \bar Wv_l=\lambda^{-1}v_{-l}+\delta\sum_{i=1}^l
--   \left(A_{l+1-i}v_{1-i}-v_{l-2i+2}\right).
--   $$
--   The subscripts are integers, and the sum is empty at $l=0$. The formula gives the explicit $\bar W$ columns needed in the derivation of admissibility; no admissibility assumption is used.
-- source:
--   The cyclotomic BMW algebra associated with the two string type B braid group, arXiv:math/0611518v3, PDF p. 6, Claim (19)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P58

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intake100.P58

open Accepted

variable {R : Type*} [CommRing R] {k : ℕ}

/-- Section 3, explicit Claim (19), PDF p.6. Integer subscripts preserve
all negative indices; at l=0 the finite sum is empty. -/
theorem claim_19 (P : NonsplitParameters R k) (hdelta : RegularDelta P) :
    ∀ l : Fin k, Wv P (orbitVector P (l.val : ℤ)) =
      (↑P.lam⁻¹ : R) • orbitVector P (-(l.val : ℤ)) +
      skeinDelta P • (∑ i ∈ Finset.Icc 1 l.val,
        (aAt P (l.val+1-i) • orbitVector P (1-(i : ℤ)) -
          orbitVector P ((l.val : ℤ)-2*(i : ℤ)+2))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P58

end
