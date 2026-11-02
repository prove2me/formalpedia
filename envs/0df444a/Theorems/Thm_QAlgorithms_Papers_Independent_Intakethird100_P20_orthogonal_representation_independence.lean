-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_orthogonal_representation_independence
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.orthogonal_representation_independence
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:48:21.159802+00:00
-- url     : https://prove2.me/theorems/41bb065d-aa70-46b9-86ff-547590e84ba7
-- title:
--   Lemma 3.6
-- statement:
--   Let $\mathcal A$ be an abelian von Neumann algebra. If $A$ has two finite orthogonal representations $A=\sum_j b_jP_j=\sum_k c_kQ_k$ by nonzero projections, then the complex-valued functions on $Q(\mathcal A)$ agree:
--
--   $$\sum_j b_j\chi_{Q_{P_j}(\mathcal A)}
--   =\sum_k c_k\chi_{Q_{Q_k}(\mathcal A)}.$$
--
--   Zero coefficients are allowed. The equality is of functions, not evaluation at the operator $A$.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 60, Lemma 3.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Lemma 3.6; de Groote, Observables I, PDF p./pp. 60.
-/
theorem orthogonal_representation_independence {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : VonNeumannAlgebra H)
    (hcomm : ∀ a b : R.toStarSubalgebra, a * b = b * a) (x : R.toStarSubalgebra)
    {m n : ℕ} (b : Fin m → ℂ) (p : Fin m → Projection R)
    (c : Fin n → ℂ) (q : Fin n → Projection R)
    (hp : IsOrthogonalRepresentation x b p) (hq : IsOrthogonalRepresentation x c q) :
    spectralSumFunction b p = spectralSumFunction c q := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
