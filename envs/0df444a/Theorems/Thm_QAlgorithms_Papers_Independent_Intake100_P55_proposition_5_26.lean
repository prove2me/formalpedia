-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_proposition_5_26
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.proposition_5_26
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:59:23.269318+00:00
-- url     : https://prove2.me/theorems/07ac040d-1179-450e-bf38-ba7499d62f4d
-- title:
--   Proposition 5.26
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   Let $k\ge1$, let $f_k\in W_{2k}$ be the recursive element of Definition 5.22, and let $S(f_k)\in W_{2k+1}$ be the same word with every generator index increased by one. For $1\le i<k$, and either sign,
--   $$\begin{aligned}g_i^{\pm1}f_k&=g_{2k-i}^{\pm1}f_k,&f_kg_i^{\pm1}&=f_kg_{2k-i}^{\pm1},\e_if_k&=e_{2k-i}f_k,&f_ke_i&=f_ke_{2k-i}.\end{aligned}$$
--   For $2\le i<k+1$, one also has
--   $$\begin{aligned}g_i^{\pm1}S(f_k)&=g_{2k+2-i}^{\pm1}S(f_k),&S(f_k)g_i^{\pm1}&=S(f_k)g_{2k+2-i}^{\pm1},\e_iS(f_k)&=e_{2k+2-i}S(f_k),&S(f_k)e_i&=S(f_k)e_{2k+2-i}.\end{aligned}$$
--   These identities express reflection across each nested contraction element.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 41, Proposition 5.26

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Proposition 5.26(1)--(4), PDF pp.41--42. Both left/right identities
and both inverse signs are retained; S(f_k) is its index-shifted word. -/
theorem proposition_5_26 (k : ℕ) (hk : 1 ≤ k) :
    (∀ i, 1 ≤ i → i < k → ∀ inv : Bool,
      ghCrossing P q false (2*k) i inv * fElement P q (2*k) 0 k =
        ghCrossing P q false (2*k) (2*k-i) inv * fElement P q (2*k) 0 k ∧
      fElement P q (2*k) 0 k * ghCrossing P q false (2*k) i inv =
        fElement P q (2*k) 0 k * ghCrossing P q false (2*k) (2*k-i) inv) ∧
    (∀ i, 1 ≤ i → i < k →
      ghContraction P q false (2*k) i * fElement P q (2*k) 0 k =
        ghContraction P q false (2*k) (2*k-i) * fElement P q (2*k) 0 k ∧
      fElement P q (2*k) 0 k * ghContraction P q false (2*k) i =
        fElement P q (2*k) 0 k * ghContraction P q false (2*k) (2*k-i)) ∧
    (∀ i, 2 ≤ i → i < k+1 → ∀ inv : Bool,
      ghCrossing P q false (2*k+1) i inv * fElement P q (2*k+1) 1 k =
        ghCrossing P q false (2*k+1) (2*k+2-i) inv * fElement P q (2*k+1) 1 k ∧
      fElement P q (2*k+1) 1 k * ghCrossing P q false (2*k+1) i inv =
        fElement P q (2*k+1) 1 k * ghCrossing P q false (2*k+1) (2*k+2-i) inv) ∧
    (∀ i, 2 ≤ i → i < k+1 →
      ghContraction P q false (2*k+1) i * fElement P q (2*k+1) 1 k =
        ghContraction P q false (2*k+1) (2*k+2-i) * fElement P q (2*k+1) 1 k ∧
      fElement P q (2*k+1) 1 k * ghContraction P q false (2*k+1) i =
        fElement P q (2*k+1) 1 k * ghContraction P q false (2*k+1) (2*k+2-i)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
