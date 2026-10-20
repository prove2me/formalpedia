-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_binary_qubit_classical_maximizer
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.binary_qubit_classical_maximizer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:41:17.156252+00:00
-- url     : https://prove2.me/theorems/a6b8f5fc-4307-469e-9502-23cf63a0471d
-- title:
--   Theorem 4(2): classical binary maximizer among qubit auxiliaries
-- statement:
--   Let $q(x,y,z)$ be any normalized law on finite alphabets, with $X=\{0,1\}$. For cq channels $X\to F$ of dimension exactly two, form $I(F;Y)-I(F;Z)$ on the factored extension $F-X-YZ$. There is a binary classical channel $X\to C_*$ whose diagonal qubit realization $F_*$ satisfies
--
--   $$
--   I(F;Y)-I(F;Z)\le I(F_*;Y)-I(F_*;Z)
--   =I(C_*;Y)-I(C_*;Z)
--   $$
--
--   for every such qubit channel $X\to F$. Thus the supremum over qubit auxiliaries is an attained classical maximum.
--
--   The dimension-two restriction is essential to the stated result; no comparison with all larger quantum dimensions is asserted.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 10, Theorem 4(2): classical binary maximizer among qubit auxiliaries

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- Theorem 4(2), PDF p.10: an attained classical diagonal qubit optimizer, compared only
with dimension-two auxiliaries. -/
theorem binary_qubit_classical_maximizer {y z : ℕ} (hy : 0 < y) (hz : 0 < z)
    (p : Law (Fin 2 × Fin y × Fin z)) :
    ∃ K : CChannel (Fin 2) (Fin 2), ∃ Q : QChannel (Fin 2) (Fin 2),
      (∀ x, Q.rho x = Matrix.diagonal (fun c => ((K x).prob c : ℂ))) ∧
      quantumDifference p Q = classicalDifference p K ∧
      ∀ E : QChannel (Fin 2) (Fin 2), quantumDifference p E ≤ quantumDifference p Q := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end
