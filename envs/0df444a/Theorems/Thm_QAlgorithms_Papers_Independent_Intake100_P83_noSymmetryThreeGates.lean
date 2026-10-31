-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_noSymmetryThreeGates
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.noSymmetryThreeGates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:18:43.425989+00:00
-- url     : https://prove2.me/theorems/2fb4ca71-b601-4889-a3d6-f2bad8729531
-- title:
--   S, CZ and x rotations generate all qubit unitaries up to global phase
-- statement:
--   Let $n\ge1$ and let $U$ be any unitary on $n$ qubits. Gates may act on arbitrary named sites. Let $\mathcal F$ contain the single-qubit gate $S=\operatorname{diag}(1,i)$, the two-qubit controlled-Z gate, and the single-qubit rotations $e^{i\theta\sigma_x}$ for $0\le\theta<2\pi$. There exist a phase $z\in\mathbb C$ and an exact finite product $W$ of these gates such that
--
--   $$
--   |z|=1,\qquad U=zW.
--   $$
--
--   This is the no-symmetry specialization of the three-family synthesis principle, including the one-qubit case.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 9, V example, unnumbered: S, CZ and x rotations

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF pp.8-9: S, CZ and arbitrary x rotations exactly generate every n-qubit unitary
up to a single global phase; n=1 is included. -/
theorem noSymmetryThreeGates (n : ℕ) (hn : 1 ≤ n)
    (U : Op (Words Bool n)) (hU : U ∈ Matrix.unitaryGroup (Words Bool n) ℂ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ W ∈ finiteGateProducts
      (sFamily n ∪ standardCZFamily n ∪ rotationFamily (liftOneQubitMatrix QAlgorithms.pauliX) n),
      U = z • W := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
