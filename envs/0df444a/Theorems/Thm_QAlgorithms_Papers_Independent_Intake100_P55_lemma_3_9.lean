-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_lemma_3_9
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.lemma_3_9
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:51:50.099714+00:00
-- url     : https://prove2.me/theorems/c354dd7f-bd74-425e-9590-792df428e1e9
-- title:
--   Lemma 3.9
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   In either presentation all the following identities hold whenever their generator indices exist. For $1\le i$ and $i+1<n$, and either sign,
--   $$g_i^{\pm1}(g_{i+1}g_i)=(g_{i+1}g_i)g_{i+1}^{\pm1},\qquad e_i(g_{i+1}g_i)=(g_{i+1}g_i)e_{i+1}.$$
--   For $i+2<n$, one also has $g_ig_{i+1}e_ie_{i+2}=g_{i+2}g_{i+1}e_ie_{i+2}$. For $1\le i<m<n$, put $D_m=g_m\cdots g_1$ and $U_m=g_1\cdots g_m$. Then
--   $$g_i^{\pm1}D_m=D_mg_{i+1}^{\pm1},\quad g_{i+1}^{\pm1}U_m=U_mg_i^{\pm1},\quad e_iD_m=D_me_{i+1},\quad e_{i+1}U_m=U_me_i.$$
--   These identities transport generators through consecutive braid words.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 18, Lemma 3.9

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Lemma 3.9(1)--(5), PDF pp.18--19. Both signs and both product
orders in the two long-word transport clauses are retained. -/
theorem lemma_3_9 (aff : Bool) (n : ℕ) :
    (∀ i, 1 ≤ i → i+1 < n → ∀ inv : Bool,
      ghCrossing P q aff n i inv * (ghCrossing P q aff n (i+1) false * ghCrossing P q aff n i false) =
      (ghCrossing P q aff n (i+1) false * ghCrossing P q aff n i false) * ghCrossing P q aff n (i+1) inv) ∧
    (∀ i, 1 ≤ i → i+1 < n →
      ghContraction P q aff n i * (ghCrossing P q aff n (i+1) false * ghCrossing P q aff n i false) =
      (ghCrossing P q aff n (i+1) false * ghCrossing P q aff n i false) * ghContraction P q aff n (i+1)) ∧
    (∀ i, 1 ≤ i → i+2 < n →
      ghCrossing P q aff n i false * ghCrossing P q aff n (i+1) false * ghContraction P q aff n i * ghContraction P q aff n (i+2) =
      ghCrossing P q aff n (i+2) false * ghCrossing P q aff n (i+1) false * ghContraction P q aff n i * ghContraction P q aff n (i+2)) ∧
    (∀ i m, 1 ≤ i → i < m → m < n → ∀ inv : Bool,
      ghCrossing P q aff n i inv * backward (fun j => ghCrossing P q aff n j false) 1 m =
        backward (fun j => ghCrossing P q aff n j false) 1 m * ghCrossing P q aff n (i+1) inv ∧
      ghCrossing P q aff n (i+1) inv * forward (fun j => ghCrossing P q aff n j false) 1 m =
        forward (fun j => ghCrossing P q aff n j false) 1 m * ghCrossing P q aff n i inv) ∧
    (∀ i m, 1 ≤ i → i < m → m < n →
      ghContraction P q aff n i * backward (fun j => ghCrossing P q aff n j false) 1 m =
        backward (fun j => ghCrossing P q aff n j false) 1 m * ghContraction P q aff n (i+1) ∧
      ghContraction P q aff n (i+1) * forward (fun j => ghCrossing P q aff n j false) 1 m =
        forward (fun j => ghCrossing P q aff n j false) 1 m * ghContraction P q aff n i) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
