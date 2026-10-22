-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P12_stabilizer_transitions
-- name    : QAlgorithms.Papers.Independent.Gap48.P12.stabilizer_transitions
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:40:32.512204+00:00
-- url     : https://prove2.me/theorems/802dea10-fab0-42ef-ae6a-5fa3e30f0533
-- title:
--   Fact 3: Bloch stabilizer transitions under T, HT, PHT
-- statement:
--   Let $|\psi\rangle\in\mathbb C^2$ be a unit vector, and let $x,y,z\in\mathbb R$ satisfy $(xX+yY+zZ)|\psi\rangle=|\psi\rangle$. All three transformed states have the following stabilizing coordinates:
--
--   $$\begin{aligned}
--   T|\psi\rangle &: \frac1{\sqrt2}(x-y,x+y,\sqrt2z),\\
--   HT|\psi\rangle &: \frac1{\sqrt2}(\sqrt2z,-x-y,x-y),\\
--   PHT|\psi\rangle &: \frac1{\sqrt2}(x+y,\sqrt2z,x-y).
--   \end{aligned}$$
--
--   A tuple $(a,b,c)$ stabilizes a state when $(aX+bY+cZ)$ acts on it as $+1$. Lean simplifies each component $(\sqrt2z)/\sqrt2$ to $z$. The theorem includes the three state-stabilization conclusions, not only their conjugation identities.
-- source:
--   Representation of Quantum Circuits with Clifford and $π/8$ Gates, arXiv:0806.3834v1, PDF p. 11, Fact 3: Bloch stabilizer transitions under T, HT, PHT

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P12

local notation "Mat" => Matrix Bool Bool ℂ

local notation "Vec" => EuclideanSpace ℂ Bool

local notation "wordMatrix" => fun (B : CircuitBasis) (w : CircuitWord) =>
  QAlgorithms.Papers.Independent.Next46.P21.wordMatrix (chronologicalInstructions B w)

/-- PDF p.11, Fact 3: all three transformed-state stabilization claims.
The √2*z components inside the printed common 1/√2 factor simplify to z. -/
theorem stabilizer_transitions (psi : Vec) (hpsi : IsState psi)
    (x y z : ℝ) (h : PauliStabilizes x y z psi) :
    PauliStabilizes ((x - y) / Real.sqrt 2) ((x + y) / Real.sqrt 2) z (act gateT psi) ∧
    PauliStabilizes z ((-x - y) / Real.sqrt 2) ((x - y) / Real.sqrt 2)
      (act (hadamard * gateT) psi) ∧
    PauliStabilizes ((x + y) / Real.sqrt 2) z ((x - y) / Real.sqrt 2)
      (act (phaseS * hadamard * gateT) psi) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P12

end
