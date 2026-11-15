-- Prove2me | Theorems.Thm_QuantumLTF_Membership_tensorSingle_offdiag
-- name    : QuantumLTF.Membership.tensorSingle_offdiag
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-14T22:08:57.85049+00:00
-- url     : https://prove2.me/theorems/564e4cb2-0d11-409e-90ef-0673b4de981b
-- title:
--   Tensor products of diagonal qubit matrices are diagonal
-- statement:
--   If every one-qubit matrix $u_i$ is diagonal, then their tensor product is diagonal. More explicitly, for distinct $b$-bit strings $y$ and $z$, some wire differs; the corresponding factor $(u_i)_{y_i,z_i}$ is zero, so the full product entry is zero.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Lemma 3.3, p. 27 (PDF p. 28), tensor-product operator used in Eq. (48).

import Mathlib
import Definitions.Def_QuantumLTF_Membership_tensorSingle

namespace QuantumLTF.Membership

open QAlgorithms

/-- A tensor product of one-qubit matrices with zero off-diagonal entries also has zero off-diagonal entries. -/
theorem tensorSingle_offdiag {b : ℕ} (u : Fin b → Matrix Bool Bool ℂ)
    (hu : ∀ i y z, y ≠ z → u i y z = 0)
    (y z : Qubits b) (hyz : y ≠ z) :
    tensorSingle u y z = 0 := by sorry

end QuantumLTF.Membership
