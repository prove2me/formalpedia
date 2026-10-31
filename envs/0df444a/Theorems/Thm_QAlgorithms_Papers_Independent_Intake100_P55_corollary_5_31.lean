-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_corollary_5_31
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.corollary_5_31
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:00:31.82569+00:00
-- url     : https://prove2.me/theorems/72d213aa-f664-4df5-abac-49cc71409fab
-- title:
--   Corollary 5.31
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   For every $k\ge0$, let $f_k$ be the recursive element of Definition 5.22, with $f_0=1$, and let $S$ shift every generator index by one. For the rank ideals of Definition 5.29,
--   $$W_{2k}^{(0)}=W_kf_kW_k,\qquad W_{2k+1}^{(1)}=W_{k+1}S(f_k)W_{k+1}.$$
--   Products denote linear spans in the ambient algebra. These describe the minimal rank ideals by smaller-level sandwich products.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 45, Corollary 5.31

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Corollary 5.31(1),(2), PDF p.45. W_(2k)^(0) and W_(2k+1)^(1)
are exactly the indicated lower-level sandwich spans. -/
theorem corollary_5_31 (k : ℕ) :
    sandwichSpan (R := R) (Set.univ : Set (OrdinaryAffineBMW P q false (2*k))) (oddContractions P q (2*k) k) =
      sandwichSpan (R := R) (bmwLevel P q false false (2*k) k : Set (OrdinaryAffineBMW P q false (2*k)))
        (fElement P q (2*k) 0 k) ∧
    sandwichSpan (R := R) (Set.univ : Set (OrdinaryAffineBMW P q false (2*k+1))) (oddContractions P q (2*k+1) k) =
      sandwichSpan (R := R) (bmwLevel P q false false (2*k+1) (k+1) : Set (OrdinaryAffineBMW P q false (2*k+1)))
        (fElement P q (2*k+1) 1 k) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
