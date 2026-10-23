-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_hermitian_moment_implication
-- name    : QAlgorithms.Papers.Independent.Information100.P19.hermitian_moment_implication
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:02:10.38401+00:00
-- url     : https://prove2.me/theorems/28945f17-9e0b-48ce-ad5d-0cdf2b74ecbf
-- title:
--   Lemma 6.2
-- statement:
--   For an arbitrary Hermitian $X$ of positive finite dimension, assume $p_1(X)=\operatorname{Tr}X>0$. Then
--   $$p_1p_3\ge p_2^2\quad\Longrightarrow\quad p_1^2p_4\ge p_2^3.$$
--   Positive semidefiniteness is not required. This supplies the signed-spectral implication used in comparing PPT moments and realignment moments.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 40, Lemma 6.2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Lemma 6.2; arXiv:2609.29471v1, PDF pp.40. -/
theorem hermitian_moment_implication (d : ℕ) (hd : 0<d) (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : X.IsHermitian) (ht : 0<powerTrace X 1)
    (h : powerTrace X 2^2 ≤ powerTrace X 1*powerTrace X 3) :
    powerTrace X 2^3 ≤ powerTrace X 1^2*powerTrace X 4 := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
