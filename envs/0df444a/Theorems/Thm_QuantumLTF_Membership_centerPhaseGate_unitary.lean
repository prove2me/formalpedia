-- Prove2me | Theorems.Thm_QuantumLTF_Membership_centerPhaseGate_unitary
-- name    : QuantumLTF.Membership.centerPhaseGate_unitary
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-14T21:20:11.588438+00:00
-- url     : https://prove2.me/theorems/792f2c68-f376-4013-9890-0c568bdae0b9
-- title:
--   The centered-grid phase gates are unitary
-- statement:
--   For every number of qubits $b$ and every wire $i$, the explicit diagonal gate `centerPhaseGate b i` has entries of complex modulus one and is therefore a unitary $2\times2$ matrix. This discharges the unitarity part of the centered-grid Fourier factorization.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Lemma 3.3, p. 27 (PDF p. 28), Eqs. (44)–(48).

import Mathlib
import Definitions.Def_QuantumLTF_Membership_centerPhaseGate

namespace QuantumLTF.Membership

/-- Each explicit one-qubit centered-grid phase gate is unitary. -/
theorem centerPhaseGate_unitary (b : ℕ) (i : Fin b) :
    centerPhaseGate b i ∈ Matrix.unitaryGroup Bool ℂ := by sorry

end QuantumLTF.Membership
