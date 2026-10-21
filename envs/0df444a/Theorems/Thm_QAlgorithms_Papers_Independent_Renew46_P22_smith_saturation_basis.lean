-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P22_smith_saturation_basis
-- name    : QAlgorithms.Papers.Independent.Renew46.P22.smith_saturation_basis
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:33:20.541138+00:00
-- url     : https://prove2.me/theorems/ff8806d4-d848-4afb-8938-60525b91ed33
-- title:
--   Smith saturation recovers the full integer relation lattice
-- statement:
--   Let $F$ be a field of characteristic zero, and let $K$ be its specified algebraic closure. Let $\alpha_1,\ldots,\alpha_n$ belong to a characteristic-zero field $K$. Put $\Lambda=\{e\in\mathbb Z^n:\sum_i e_i\alpha_i=0\}$ and $\Lambda_{\mathbb Q}=\{e\in\mathbb Q^n:\sum_i e_i\alpha_i=0\}$. Let $B\in\mathbb Z^{m\times n}$ have rows that form a rational basis of the entire space $\Lambda_{\mathbb Q}$. Suppose $m\le n$ and $P B Q=S$ is a Smith form, with integral unimodular $P,Q$ and positive diagonal factors $d_1,\ldots,d_m$. The case $m=0$ is allowed.
--
--   Let $S^\ast$ be the rectangular diagonal matrix with $m$ diagonal entries equal to $1$, and define $A=P^{-1}S^\ast Q^{-1}$. Then
--
--   $$\operatorname{row}_i(A)\in\Lambda,\qquad P A Q=S^\ast,$$
--
--   and the rows of $A$ form a basis of $\Lambda_{\mathbb Q}$ over $\mathbb Q$ and a basis of $\Lambda$ over $\mathbb Z$. In particular, the Smith form of $A$ is $S^\ast$.
--
--   This gives the explicit saturation of an integral rational relation basis; no numerical running-time claim is made.
-- source:
--   Constructing algebraic groups from their Lie algebras, arXiv:math/0612557v1, PDF p. 6, Unnumbered construction following Lemma 6

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P22

open scoped BigOperators Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing

section Relations

variable {K : Type*} [Field K] [CharZero K] {m n : ℕ}

variable {F : Type*} [Field F] [hcharF : CharZero F] [Algebra F K] [hclosureF : IsAlgClosure F K]

section

include hcharF hclosureF

/-- Unnumbered saturation result after Lemma 6, PDF p.6, including all four conclusions. -/
theorem smith_saturation_basis (alpha : Fin n → K)
    (B : Matrix (Fin m) (Fin n) ℤ) (hB : RationalRowsBasis alpha B) (D : SmithData B) :
    (∀ i, saturationMatrix D i ∈ relationKernel ℤ alpha) ∧
    RationalRowsBasis alpha (saturationMatrix D) ∧
    ((D.P : Matrix (Fin m) (Fin m) ℤ) * saturationMatrix D *
      (D.Q : Matrix (Fin n) (Fin n) ℤ) = rectangularDiagonal m n (fun _ => 1)) ∧
    IntegerRowsBasis alpha (saturationMatrix D) := by sorry

end

end Relations

end QAlgorithms.Papers.Independent.Renew46.P22

end
