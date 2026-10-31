-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_proposition_5_28
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.proposition_5_28
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:59:46.603648+00:00
-- url     : https://prove2.me/theorems/53166224-da1b-4f43-8df2-3f1b99021584
-- title:
--   Proposition 5.28
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   For every $k\ge0$, let $f_k$ be the recursive element of Definition 5.22, extended by $f_0=1$, and let $S$ shift every generator index by one. Then
--   $$\begin{aligned}W_{2k}f_k&=W_kf_k,&f_kW_{2k}&=f_kW_k,\W_{2k+1}S(f_k)&=W_{k+1}S(f_k),&S(f_k)W_{2k+1}&=S(f_k)W_{k+1}.\end{aligned}$$
--   All products are linear spans and smaller levels are canonical images. These identify the relevant left and right contraction submodules at lower levels.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 44, Proposition 5.28

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Proposition 5.28(1),(2), PDF p.44, both left and right product spans.
The harmless k=0 extension uses f_0=1 and W_0=R. -/
theorem proposition_5_28 (k : ℕ) :
    rightSpan (R := R) (Set.univ : Set (OrdinaryAffineBMW P q false (2*k))) (fElement P q (2*k) 0 k) =
      rightSpan (R := R) (bmwLevel P q false false (2*k) k : Set (OrdinaryAffineBMW P q false (2*k)))
        (fElement P q (2*k) 0 k) ∧
    leftSpan (R := R) (fElement P q (2*k) 0 k) (Set.univ : Set (OrdinaryAffineBMW P q false (2*k))) =
      leftSpan (R := R) (fElement P q (2*k) 0 k)
        (bmwLevel P q false false (2*k) k : Set (OrdinaryAffineBMW P q false (2*k))) ∧
    rightSpan (R := R) (Set.univ : Set (OrdinaryAffineBMW P q false (2*k+1))) (fElement P q (2*k+1) 1 k) =
      rightSpan (R := R) (bmwLevel P q false false (2*k+1) (k+1) : Set (OrdinaryAffineBMW P q false (2*k+1)))
        (fElement P q (2*k+1) 1 k) ∧
    leftSpan (R := R) (fElement P q (2*k+1) 1 k) (Set.univ : Set (OrdinaryAffineBMW P q false (2*k+1))) =
      leftSpan (R := R) (fElement P q (2*k+1) 1 k)
        (bmwLevel P q false false (2*k+1) (k+1) : Set (OrdinaryAffineBMW P q false (2*k+1))) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
