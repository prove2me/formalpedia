-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_parity_fact4
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.parity_fact4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:41:55.160253+00:00
-- url     : https://prove2.me/theorems/8699ec7e-0dc4-45a9-8887-34a82275692b
-- title:
--   Fact 4: parity transitions from T1/T2 under HT and PHT
-- statement:
--   For a word $C$ with $\ell=t(C)$, define its class $T_j$ through a stabilizer of $f_u(C)|0\rangle$ of the form
--
--   $$2^{-\ell/2}(x_a+x_b\sqrt2,\ y_a+y_b\sqrt2,\ z_a+z_b\sqrt2),$$
--
--   with integer coefficients in the order $(x_a,x_b,y_a,y_b,z_a,z_b)$. In $T_1$ exactly $x_b,z_b$ are odd; in $T_2$ exactly $y_b,z_b$ are odd; all other coordinates are even. Then
--
--   $$C\in T_1\cup T_2\quad\Longrightarrow\quad HTC\in T_2,\quad PHTC\in T_1.$$
--
--   The target denominators use $\ell+1$ because both prefixes add one literal $T$. Class membership is tied to the actual output stabilizer, and no normality premise is required for this coefficient transition.
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 12, Fact 4: parity transitions from T1/T2 under HT and PHT

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.12, Fact 4: T1/T2 --HT--> T2 and --PHT--> T1.
Membership uses actual circuit stabilization at its actual T-count. -/
theorem parity_fact4 (C : CircuitWord) (h : InParityClass 0 C ∨ InParityClass 1 C) :
    InParityClass 1 (.h :: .t :: C) ∧ InParityClass 0 (.p :: .h :: .t :: C) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
