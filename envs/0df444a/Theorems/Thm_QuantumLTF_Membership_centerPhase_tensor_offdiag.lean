-- Prove2me | Theorems.Thm_QuantumLTF_Membership_centerPhase_tensor_offdiag
-- name    : QuantumLTF.Membership.centerPhase_tensor_offdiag
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T00:01:39.320323+00:00
-- url     : https://prove2.me/theorems/4b0d2017-10d4-45e4-891f-0c27fcdc7e1f
-- title:
--   The centered phase tensor is diagonal
-- statement:
--   For distinct $b$-qubit computational-basis labels $y$ and $z$, the corresponding entry of the tensor product of the explicit centered-grid phase gates is zero. Thus the correction operator appearing in Lemma 3.3 is diagonal.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Lemma 3.3, p. 27 (PDF p. 28), Eq. (48).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_tensorSingle
import Definitions.Def_QuantumLTF_Membership_centerPhaseGate

namespace QuantumLTF.Membership

open QAlgorithms

/-- The tensor product of the explicit centered-grid phase gates has zero off-diagonal entries. -/
theorem centerPhase_tensor_offdiag {b : ℕ} (y z : Qubits b) (hyz : y ≠ z) :
    tensorSingle (centerPhaseGate b) y z = 0 := by sorry

end QuantumLTF.Membership
