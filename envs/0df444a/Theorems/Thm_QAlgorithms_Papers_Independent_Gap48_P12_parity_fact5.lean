-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_parity_fact5
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.parity_fact5
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:42:37.348995+00:00
-- url     : https://prove2.me/theorems/89417bfe-c219-4ae1-9ad1-506d9fa50e1a
-- title:
--   Fact 5: parity transition from T1/T2 under T
-- statement:
--   For a circuit word $C$ at its actual level $\ell=t(C)$, use the integer stabilizer representation $2^{-\ell/2}(x_a+x_b\sqrt2,y_a+y_b\sqrt2,z_a+z_b\sqrt2)$ of $f_u(C)|0\rangle$. Classes $T_1,T_2,T_3$ have respectively the odd-coordinate sets $\{x_b,z_b\}$, $\{y_b,z_b\}$, and $\{x_b,y_b\}$, with all remaining coordinates even. Then
--
--   $$C\in T_1\cup T_2\quad\Longrightarrow\quad TC\in T_3.$$
--
--   The target is interpreted at level $\ell+1$. This is Fact 5 on page 13.
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 13, Fact 5: parity transition from T1/T2 under T

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.13, Fact 5: T1/T2 --T--> T3. -/
theorem parity_fact5 (C : CircuitWord) (h : InParityClass 0 C ∨ InParityClass 1 C) :
    InParityClass 2 (.t :: C) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
