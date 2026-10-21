-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P22_relationBasis_iff_smithFactors_one
-- name    : QAlgorithms.Papers.Independent.Renew46.P22.relationBasis_iff_smithFactors_one
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:32:54.155128+00:00
-- url     : https://prove2.me/theorems/8b25aa1a-8236-4908-a50f-69267b72fb9f
-- title:
--   An integral relation basis is detected by its Smith factors
-- statement:
--   Let $F$ be a field of characteristic zero, and let $K$ be its specified algebraic closure. Let $\alpha_1,\ldots,\alpha_n$ belong to a characteristic-zero field $K$. Put $\Lambda=\{e\in\mathbb Z^n:\sum_i e_i\alpha_i=0\}$ and $\Lambda_{\mathbb Q}=\{e\in\mathbb Q^n:\sum_i e_i\alpha_i=0\}$. Let $B\in\mathbb Z^{m\times n}$ have rows that form a rational basis of the entire space $\Lambda_{\mathbb Q}$. Suppose $m\le n$ and $P B Q=S$ is a Smith form, with integral unimodular $P,Q$ and positive diagonal factors $d_1,\ldots,d_m$. The case $m=0$ is allowed.
--
--   Then
--
--   $$\text{the rows of }B\text{ form a }\mathbb Z\text{-basis of }\Lambda\quad\Longleftrightarrow\quad d_i=1\text{ for every }i.$$
--
--   This tests whether an integral rational basis already generates the complete relation lattice.
-- source:
--   Constructing algebraic groups from their Lie algebras, arXiv:math/0612557v1, PDF p. 5, Lemma 6

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

/-- Lemma 6, PDF pp.5–6. The rows are already a rational basis of the complete kernel. -/
theorem relationBasis_iff_smithFactors_one (alpha : Fin n → K)
    (B : Matrix (Fin m) (Fin n) ℤ) (hB : RationalRowsBasis alpha B) (D : SmithData B) :
    IntegerRowsBasis alpha B ↔ ∀ i, D.factors i = 1 := by sorry

end

end Relations

end QAlgorithms.Papers.Independent.Renew46.P22

end
