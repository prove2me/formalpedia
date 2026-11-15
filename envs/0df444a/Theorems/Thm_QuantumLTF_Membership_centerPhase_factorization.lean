-- Prove2me | Theorems.Thm_QuantumLTF_Membership_centerPhase_factorization
-- name    : QuantumLTF.Membership.centerPhase_factorization
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-14T20:38:26.079427+00:00
-- url     : https://prove2.me/theorems/c264dfbb-7fda-4484-8585-11689073dc16
-- title:
--   Explicit phase factorization of the centered-grid QFT
-- statement:
--   For $b\ge0$, let $U_b=\bigotimes_{i=0}^{b-1}u_i$, where $u_i$ is the explicit diagonal gate `centerPhaseGate(b,i)`. Each $u_i$ is unitary and
--
--   $$
--   \operatorname{QFT}_{G_b}=U_b\,\operatorname{QFT}_b\,U_b.
--   $$
--
--   This strengthens Lemma 3.3 by specifying the one-qubit gates. It reduces the proof to expanding $2^b\hat j\hat k$, factoring the affine phases over the binary digits of $j$ and $k$, and checking diagonal unitarity.
--
--   **Formalization Note** At $b=0$, all matrices are the unique $1\times1$ identity and the family of gates is empty.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, Lemma 3.3 and Eqs. (44)–(48), p. 27 (PDF p. 28); explicit gate choice obtained by expanding the displayed phases

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QuantumLTF_Membership_tensorSingle
import Definitions.Def_QuantumLTF_Membership_centerPhaseGate

namespace QuantumLTF.Membership

open QAlgorithms

/-- The centered-grid Fourier transform is the ordinary qubit QFT conjugated on both sides by the explicit tensor product of `centerPhaseGate`s. -/
theorem centerPhase_factorization (b : ℕ) :
    (∀ i : Fin b, centerPhaseGate b i ∈ Matrix.unitaryGroup Bool ℂ) ∧
      gridQFT b = tensorSingle (centerPhaseGate b) * qftQubits b *
        tensorSingle (centerPhaseGate b) := by sorry

end QuantumLTF.Membership
