-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_corollary_3_21
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.corollary_3_21
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:57:59.150983+00:00
-- url     : https://prove2.me/theorems/28775739-6399-411c-a23f-fb42c72966fa
-- title:
--   Corollary 3.21
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   For every $n\ge1$, inside $W_{n+1}$,
--   $$W_{n+1}e_n=W_ne_n.$$
--   Here the smaller algebra means its canonical generator image and products denote linear spans. This is the ordinary version of the preceding-level right-ideal identity.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 25, Corollary 3.21

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Corollary 3.21, PDF p.25, ordinary version of the right-ideal equality. -/
theorem corollary_3_21 (n : ℕ) (hn : 1 ≤ n) :
    rightSpan (R := R) (Set.univ : Set (OrdinaryAffineBMW P q false (n+1))) (ghContraction P q false (n+1) n) =
    rightSpan (R := R) (bmwLevel P q false false (n+1) n : Set (OrdinaryAffineBMW P q false (n+1)))
      (ghContraction P q false (n+1) n) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
