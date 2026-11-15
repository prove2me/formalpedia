-- Prove2me | Theorems.Thm_QuantumLTF_Membership_centerPhase_tensor_diag
-- name    : QuantumLTF.Membership.centerPhase_tensor_diag
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T02:11:01.973283+00:00
-- url     : https://prove2.me/theorems/fd55ca30-0a0a-43c1-96d7-bff3d66c390f
-- title:
--   Diagonal entry of the centered phase tensor
-- statement:
--   For $N=2^b$ and the centered-grid shift $c=-1/2+1/(2N)$, the diagonal entry of the tensor product of all centered phase gates at basis label $z$ is the complex exponential with exponent $c bitsToNat(z)+Nc^2/2$. This combines the per-wire exponential factors into one phase.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Lemma 3.3, p. 27 (PDF p. 28), Eqs. (44)–(48).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_tensorSingle
import Definitions.Def_QuantumLTF_Membership_centerPhaseGate

namespace QuantumLTF.Membership

open QAlgorithms

/-- The diagonal tensor entry is the exponential of the collapsed centered phase. -/
theorem centerPhase_tensor_diag (b : ℕ) (z : Qubits b) :
    let N : ℂ := (2 : ℂ) ^ b
    let c : ℂ := -(1 / 2) + 1 / (2 * N)
    tensorSingle (centerPhaseGate b) z z =
      Complex.exp (2 * Real.pi * Complex.I *
        (c * (bitsToNat z : ℂ) + N * c ^ 2 / 2)) := by sorry

end QuantumLTF.Membership
