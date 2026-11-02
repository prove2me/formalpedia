-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P57_completeness
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P57.completeness
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:11:00.478063+00:00
-- url     : https://prove2.me/theorems/59658cb9-825e-4157-a667-c3222d114eef
-- title:
--   Main properties (iii): completeness when the bond dimension may grow exponentially
-- statement:
--   Let $N\ge1$ and let $\psi$ be any unit vector in $(\mathbb C^2)^{\otimes N}$. There exist an integer bond dimension $D$ and periodic trace tensors $A$ such that
--
--   $$1\le D\le2^N,\qquad R(A,0,I)=\psi.$$
--
--   The graph weights and final local rotations can therefore be chosen trivial. This is an exact representability statement with exponential bond dimension allowed.
-- source:
--   Renormalization algorithm with graph enhancement, arXiv:0802.1211v1, PDF p. 2, Main properties (iii): completeness when the bond dimension may grow exponentially

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57

noncomputable section

open scoped ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Intakethird100.P57

attribute [local instance] Classical.propDecidable

/-- PDF p.2, Main properties (iii): exact completeness, explicitly allowing exponential D.
The graph and rotations may be chosen trivial, with the periodic trace convention retained. -/
theorem completeness (N : ℕ) (hN : 1 ≤ N) (v : EuclideanSpace ℂ (Qubits N))
    (hv : IsState v) :
    ∃ D : ℕ, 1 ≤ D ∧ D ≤ 2 ^ N ∧ ∃ A : Tensors N D,
      rage A (emptyPhaseGraph N) (fun _ => 1) = v := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P57

end
