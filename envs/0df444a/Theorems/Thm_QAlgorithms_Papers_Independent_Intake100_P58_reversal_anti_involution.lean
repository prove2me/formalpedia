-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P58_reversal_anti_involution
-- name    : QAlgorithms.Papers.Independent.Intake100.P58.reversal_anti_involution
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:03:43.408764+00:00
-- url     : https://prove2.me/theorems/c9b25687-e8bf-4612-b3b7-fc98164a7a68
-- title:
--   Section 2, unnumbered remark (7): reversal anti-involution
-- statement:
--   Let $k\ge1$ and let $R$ be a commutative unital ring. Choose units $q_0,q,\lambda\in R^\times$, coefficients $q_1,\ldots,q_{k-1}\in R$, and $A_0,\ldots,A_{k-1}\in R$. Put $\delta=q-q^{-1}$ and assume $\lambda-\lambda^{-1}=\delta(1-A_0)$. Let $B=B_2^k(R)$ be the unital associative algebra on invertible $Y,X$ and an element $e$, with relations (1)–(6) of Definition 2.1. In particular, $Y^k=\sum_{i=0}^{k-1}q_iY^i$, $X-X^{-1}=\delta(1-e)$, $XYXY=YXYX$, $Xe=eX=\lambda e$, $YXYe=eYXY=\lambda^{-1}e$, and $eY^me=A_me$ for $0\le m<k$.
--
--   Assume multiplication by $\delta$ on $R$ is injective (Assumption 2.2). Neither $A_0$ nor $\delta$ need be units, and the cyclotomic polynomial need not split.
--
--   There is an $R$-linear algebra anti-isomorphism $*:B\to B$ satisfying
--   $$
--   (ab)^*=b^*a^*,\qquad (a^*)^*=a,\qquad Y^*=Y,\quad X^*=X,\quad e^*=e.
--   $$
--   The map preserves the unit and the scalars. It is the reversal anti-involution used to define the right tensor action in Section 4. No admissibility assumption is made.
-- source:
--   The cyclotomic BMW algebra associated with the two string type B braid group, arXiv:math/0611518v3, PDF p. 4, Remark (7)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P58

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intake100.P58

open Accepted

variable {R : Type*} [CommRing R] {k : ℕ}

/-- Section 2, equation (7), PDF p.4. This is reversal: it fixes Y,X,e
and is an involutive algebra anti-isomorphism, without admissibility. -/
theorem reversal_anti_involution (P : NonsplitParameters R k) (hdelta : RegularDelta P) :
    ∃ star : TwoStrandBMW P ≃ₐ[R] (TwoStrandBMW P)ᵐᵒᵖ,
      (∀ a, MulOpposite.unop (star (MulOpposite.unop (star a))) = a) ∧
      star (y P) = MulOpposite.op (y P) ∧
      star (x P) = MulOpposite.op (x P) ∧
      star (e P) = MulOpposite.op (e P) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P58

end
