-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P58_companion_inverse_recurrence_bases
-- name    : QAlgorithms.Papers.Independent.Intake100.P58.companion_inverse_recurrence_bases
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:05:46.023374+00:00
-- url     : https://prove2.me/theorems/ca9379de-d559-490e-852a-8154a1e790ec
-- title:
--   Section 3, unnumbered (10)-(13): inverse, recurrence and shifted bases
-- statement:
--   Let $k\ge1$ and let $R$ be a commutative unital ring. Choose units $q_0,q,\lambda\in R^\times$, coefficients $q_1,\ldots,q_{k-1}\in R$, and $A_0,\ldots,A_{k-1}\in R$. Put $\delta=q-q^{-1}$ and assume $\lambda-\lambda^{-1}=\delta(1-A_0)$. Let $B=B_2^k(R)$ be the unital associative algebra on invertible $Y,X$ and an element $e$, with relations (1)–(6) of Definition 2.1. In particular, $Y^k=\sum_{i=0}^{k-1}q_iY^i$, $X-X^{-1}=\delta(1-e)$, $XYXY=YXYX$, $Xe=eX=\lambda e$, $YXYe=eYXY=\lambda^{-1}e$, and $eY^me=A_me$ for $0\le m<k$.
--
--   Assume multiplication by $\delta$ on $R$ is injective (Assumption 2.2). Neither $A_0$ nor $\delta$ need be units, and the cyclotomic polynomial need not split.
--
--   Let $V=R^k$ with its standard basis $v_0,\ldots,v_{k-1}$. The operators $\bar Y,\bar X,\bar E$ are the specific maps (8)–(17): $\bar Yv_i=v_{i+1}$ for $i<k-1$, $\bar Yv_{k-1}=\sum_{i=0}^{k-1}q_iv_i$, $\bar Xv_0=\lambda v_0$, $\bar Xv_1=\lambda^{-1}\bar Y^{-1}v_0$ when $k>1$, $\bar Xv_i=\bar Y^{-1}\bar Xv_{i-1}-\delta v_{i-2}+\delta A_{i-1}\bar Y^{-1}v_0$ for $2\le i<k$, and $\bar Ev_i=A_iv_0$. Define $\bar W=\bar X-\delta\operatorname{id}_V+\delta\bar E$ and $v_s=\bar Y^sv_0$ for every integer $s$, using the explicit inverse (10)–(11).
--
--   The displayed companion map is invertible, and its inverse is
--   $$
--   \bar Y^{-1}v_i=v_{i-1}\ (1\le i<k),\qquad
--   \bar Y^{-1}v_0=-q_0^{-1}\sum_{i=0}^{k-1}q_{i+1}v_i,\qquad q_k=-1.
--   $$
--   Both compositions with $\bar Y$ equal the identity. The integer orbit agrees with the given standard vectors for $0\le i<k$, and for every integer $s$,
--   $$
--   \sum_{l=0}^kq_l\bar Y^lv_s=0.
--   $$
--   For every integer $r$, the family
--   $$
--   (v_r,v_{r+1},\ldots,v_{r+k-1})
--   $$
--   is a basis of $V$. Empty sums have value zero. These conclusions justify all negative-index and shifted tensor coordinates used later.
-- source:
--   The cyclotomic BMW algebra associated with the two string type B braid group, arXiv:math/0611518v3, PDF p. 5, Equations (10)–(13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P58

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intake100.P58

open Accepted

variable {R : Type*} [CommRing R] {k : ℕ}

/-- Section 3, equations (10)--(13), PDF p.5. This includes both inverse
identities, the inverse columns, the orbit convention, the signed recurrence,
and the specified shifted bases, without admissibility. -/
theorem companion_inverse_recurrence_bases (P : NonsplitParameters R k) (hdelta : RegularDelta P) :
    Yv P * YvInv P = 1 ∧ YvInv P * Yv P = 1 ∧
    (∀ i : Fin k, 1 ≤ i.val → YvInv P (vNat P i.val) = vNat P (i.val-1)) ∧
    YvInv P (vNat P 0) =
      -(↑P.constant⁻¹ : R) • (∑ i : Fin k, qAt P (i.val+1) • vNat P i.val) ∧
    (∀ i : Fin k, orbitVector P (i.val : ℤ) = vNat P i.val) ∧
    (∀ i : ℤ, (∑ l ∈ Finset.range (k+1), qAt P l • (Yv P ^ l) (orbitVector P i)) = 0) ∧
    (∀ l : ℤ, ∃ b : Module.Basis (Fin k) R (CompanionModule P),
      ∀ i : Fin k, b i = orbitVector P (l + (i.val : ℤ))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P58

end
