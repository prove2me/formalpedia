-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P10_generalRankIdentity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P10.generalRankIdentity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:07:36.806985+00:00
-- url     : https://prove2.me/theorems/3ad57475-575f-4a8e-9b13-f9278510de4b
-- title:
--   Lemma 1: rank identity and inequality with a Moore–Penrose inverse
-- statement:
--   Let $m\ge0$ and let $A,B$ be real $m\times m$ matrices with $B^T=-B$ and $A-iB\succeq0$ as a complex Hermitian matrix. Let $A^+$ denote the Moore–Penrose inverse. With all ranks taken over $\mathbb C$,
--
--   $$
--   2\operatorname{rank}(A-iB)=\operatorname{rank}A+
--   \operatorname{rank}(A-BA^+B^T),\qquad
--   \operatorname{rank}B\ge\operatorname{rank}A-\operatorname{rank}(A-BA^+B^T).
--   $$
--
--   The lemma applies to singular $A$ and gives the general matrix identity behind the channel mode-count formulas. The full positivity condition implies that $A$ is symmetric positive semidefinite; separate positivity of $A$ alone would not suffice.
-- source:
--   The optimal unitary dilation for bosonic Gaussian channels, arXiv:1009.1108v1, PDF p. 7, Appendix A, Lemma 1, Eqs.(A1)–(A3)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P10

/-- Appendix A, Lemma 1, PDF pp.7–8, Eqs.(A1)–(A3). The printed `Gl` does
not impose invertibility: the proof explicitly allows singular `A`.
The full complex positivity condition is essential. -/
theorem generalRankIdentity {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    (hB : B.transpose = -B)
    (hCP : (complexify A - Complex.I • complexify B).PosSemidef) :
    (2 * (complexify A - Complex.I • complexify B).rank =
      (complexify A).rank + (complexify (rankResidual A B)).rank) ∧
    (((complexify A).rank : ℤ) - ((complexify (rankResidual A B)).rank : ℤ) ≤
      ((complexify B).rank : ℤ)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P10

end
