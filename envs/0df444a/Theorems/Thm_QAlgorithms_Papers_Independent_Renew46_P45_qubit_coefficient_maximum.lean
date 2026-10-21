-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P45_qubit_coefficient_maximum
-- name    : QAlgorithms.Papers.Independent.Renew46.P45.qubit_coefficient_maximum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:45:40.323931+00:00
-- url     : https://prove2.me/theorems/d099c4d0-8c99-49fc-8878-a74b7f1974b5
-- title:
--   Qubit coefficient maximum and unique maximizing spin labels
-- statement:
--   Let $N\ge1$ and $M>N$. Consider actual irreducible unitary $U(2)$ carriers $H_m,H_n$ with dominant integral highest weights $m=(m_1,m_2)$ and $n=(n_1,n_2)$, an isometric intertwining inclusion $H_m\hookrightarrow(\mathbb C^2)^{\otimes M}$, and an isometric intertwiner $\operatorname{Sym}^N\mathbb C^2\hookrightarrow H_m\otimes H_n$. Thus representation occurrence, including the usual parity conditions, is part of admissibility. Put $\alpha=(m_1-m_2)/2$, $\beta=(n_1-n_2)/2$ and $\gamma=N/2$. The Casimir coefficient is
--   $$
--   \omega=\frac12+\frac{\alpha(\alpha+1)-\beta(\beta+1)}{2\gamma(\gamma+1)}\le\frac{M+2}{N+2}.
--   $$
--   An admissible block attains this value, and an admissible block attains it if and only if
--   $$
--   \alpha=M/2,\qquad\beta=(M-N)/2.
--   $$
--   The equality characterization concerns irreducible spin labels, not arbitrary cloning devices or a unique choice of intertwiner.
-- source:
--   Optimal Cloning of Pure States, Judging Single Clones, arXiv:quant-ph/9807010v1, PDF p. 7, §III D, Eq.(19)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Renew46.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P45.unitaryMeasurable

/-- PDF p.7 Eq.(19): qubit maximum and uniqueness of SPIN LABELS.
Actual representation occurrence enforces parity and triangle conditions;
the incomplete printed numerical equivalences are not used. -/
theorem qubit_coefficient_maximum (N M : ℕ) (hN : 1 ≤ N) (hNM : N < M) :
    (∃ B : CloningBlock 2 N M, ∃ m n : Fin 2 → ℤ,
      HasHighestWeight B.pa m ∧ HasHighestWeight B.pb n ∧
      weightCoefficient N m n = ((M : ℝ) + 2) / ((N : ℝ) + 2)) ∧
    ∀ B : CloningBlock 2 N M, ∀ m n : Fin 2 → ℤ,
      HasHighestWeight B.pa m → HasHighestWeight B.pb n →
      weightCoefficient N m n ≤ ((M : ℝ) + 2) / ((N : ℝ) + 2) ∧
      (weightCoefficient N m n = ((M : ℝ) + 2) / ((N : ℝ) + 2) ↔
        m 0 - m 1 = (M : ℤ) ∧ n 0 - n 1 = (M : ℤ) - N) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P45

end
