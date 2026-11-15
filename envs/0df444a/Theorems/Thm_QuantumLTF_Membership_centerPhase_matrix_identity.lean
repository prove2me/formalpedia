-- Prove2me | Theorems.Thm_QuantumLTF_Membership_centerPhase_matrix_identity
-- name    : QuantumLTF.Membership.centerPhase_matrix_identity
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-14T21:24:55.637212+00:00
-- url     : https://prove2.me/theorems/ad54191d-da4b-4f5f-b8ab-1c5a1b4854ca
-- title:
--   Centered-grid QFT phase identity
-- statement:
--   For every $b$, conjugating the ordinary $b$-qubit Fourier matrix on both sides by the tensor product of the explicit diagonal `centerPhaseGate`s produces the Fourier transform on the centered grid. Entrywise, this is the expansion $N(j/N+c)(k/N+c)=jk/N+c(j+k)+Nc^2$, with the affine phases decomposed according to the binary digits of $j$ and $k$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Lemma 3.3, p. 27 (PDF p. 28), Eqs. (44)–(48).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QuantumLTF_Membership_tensorSingle
import Definitions.Def_QuantumLTF_Membership_centerPhaseGate

namespace QuantumLTF.Membership

open QAlgorithms

/-- The entrywise phase identity converting the ordinary qubit QFT into the centered-grid QFT. -/
theorem centerPhase_matrix_identity (b : ℕ) :
    gridQFT b = tensorSingle (centerPhaseGate b) * qftQubits b *
      tensorSingle (centerPhaseGate b) := by sorry

end QuantumLTF.Membership
