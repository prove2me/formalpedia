-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_parity_fact6
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.parity_fact6
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:43:17.754183+00:00
-- url     : https://prove2.me/theorems/2cf2e83e-de34-425f-9ded-684ef357304f
-- title:
--   Fact 6: four parity transition clauses
-- statement:
--   At level $\ell=t(C)$, classify the actual stabilizer of $f_u(C)|0\rangle$ by its integer coefficients in $2^{-\ell/2}(x_a+x_b\sqrt2,y_a+y_b\sqrt2,z_a+z_b\sqrt2)$. The odd-coordinate sets defining $T_4,T_5,T_6,T_7,T_8,T_9$ are respectively $\{x_b,y_a,z_a\}$, $\{x_a,y_b,z_a\}$, $\{x_a,y_a,z_b\}$, all coordinates except $x_a$, all except $y_a$, and all except $z_a$; every coordinate outside its odd set is even. All four clauses hold:
--
--   $$\begin{aligned}
--   C\in T_4\cup T_5&\Rightarrow HTC\in T_7,\quad PHTC\in T_8,\\
--   C\in T_7\cup T_8&\Rightarrow HTC\in T_4,\quad PHTC\in T_5,\\
--   C\in T_4\cup T_5&\Rightarrow TC\in T_9,\\
--   C\in T_7\cup T_8&\Rightarrow TC\in T_6.
--   \end{aligned}$$
--
--   Every target is at level $\ell+1$. The conclusions specify each actual class, retaining all of Fact 6.
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 13, Fact 6: four parity transition clauses

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.13, Fact 6: all four clauses, with all targets evaluated at
one higher T-count by the circuit-prefix definitions. -/
theorem parity_fact6 (C : CircuitWord) :
    ((InParityClass 3 C ∨ InParityClass 4 C) →
      InParityClass 6 (.h :: .t :: C) ∧ InParityClass 7 (.p :: .h :: .t :: C)) ∧
    ((InParityClass 6 C ∨ InParityClass 7 C) →
      InParityClass 3 (.h :: .t :: C) ∧ InParityClass 4 (.p :: .h :: .t :: C)) ∧
    ((InParityClass 3 C ∨ InParityClass 4 C) → InParityClass 8 (.t :: C)) ∧
    ((InParityClass 6 C ∨ InParityClass 7 C) → InParityClass 5 (.t :: C)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
