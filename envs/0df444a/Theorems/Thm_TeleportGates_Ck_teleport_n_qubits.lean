-- Prove2me | Theorems.Thm_TeleportGates_Ck_teleport_n_qubits
-- name    : TeleportGates.Ck.teleport_n_qubits
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:24.629215+00:00
-- url     : https://prove2.me/theorems/39fcaef6-8c08-4760-9f8a-ed51b857178c
-- title:
--   $n$-qubit teleportation through $|\Psi^n\rangle$: output $2^{-n}R_{xz}\psi$, uniform outcomes
-- statement:
--   Let $n\ge0$, $\psi$ a vector of $n$ qubits and $x,z\in\{0,1\}^n$. Measure input qubit $i$ together with upper qubit $i$ of $|\Psi^n\rangle=(|00\rangle+|11\rangle)^{\otimes n}$ in the Bell basis, for each $i$, with outcome $(x_i,z_i)$. Then the lower register is left in
--
--   $$(\langle\beta_{xz}|\otimes I)(\psi\otimes\Psi^n)=2^{-n}R_{xz}\,\psi,\qquad R_{xz}=\bigotimes_{i}X^{x_i}Z^{z_i},$$
--
--   and every outcome has probability $\|\psi\|^2/4^n$.
--
--   This is the multi-qubit teleportation obtained by replicating the one-qubit circuit, the case $U=I$ of gate teleportation.
--
--   Differences from the source:
--   - encoding: Bell vectors |0x⟩ + (−1)^z|1x̄⟩ and EPR pairs |00⟩ + |11⟩ with normalizations suppressed (p. 2) → normalized Bell vectors and EPR pairs (each factor 1/√2); the post-measurement state is the unnormalized contraction, so the identity carries an explicit constant; reason: fixes the constants; the paper's |ψout⟩ is this vector up to normalization
--   - reading: |α⟩ and one qubit of |Ψ⟩ are measured together in the Bell basis |0x⟩ + (−1)^z|1x̄⟩ (p. 1) → in |0x⟩ + (−1)^z|1x̄⟩ the first ket is the teleported qubit, the second the EPR half; reason: the paper names |α⟩ first; swapping the factors changes the Pauli frame by a reordering and a phase
--   - reading: Bell basis measurements on [the input] and the n upper qubits of |Ψn_U⟩ (p. 3) → input qubit i is measured with upper qubit i, giving outcome bits (x_i, z_i); reason: the natural wire-by-wire pairing of the paper's n replicated teleportation circuits (p. 1)
--   - reading: R_xz, an operator in C1 which depends on the outcomes xz (not written out); for one qubit 'X, Y, or Z', 00 the identity → the explicit R_xz = ⊗_i X^{x_i} Z^{z_i} (Z first), with XZ = −iY for x_i = z_i = 1; reason: this is the frame the p. 1 Bell basis (first ket = teleported qubit) and |00⟩ + |11⟩ give, checked by hand and by a proved sanity check for n = 1; the paper's 'Y' is −iY up to a global phase
--   - generalization: an input state |ψ⟩ (a unit vector) → |ψ⟩ any vector of the input register; reason: the identities are linear in the input; for a unit vector they are the paper's statement
--   - generalization: 'a (uniformly distributed) random two-bit classical result' (p. 1, one qubit) → every n-qubit outcome (x, z) has probability ‖ψ‖²/4ⁿ; reason: the paper states uniformity for one qubit and replicates the circuit; the n-qubit clause specializes to it at n = 1
-- source:
--   Gottesman, Chuang, Quantum teleportation is a universal computational primitive, arXiv:quant-ph/9908010v1, §I, unnumbered, p. 1 ('Replication of this circuit allows teleportation of multiple qubits'); |Ψn⟩ from §II, p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_TeleportGates_Ck_bellVec
import Definitions.Def_TeleportGates_Ck_eprState
import Definitions.Def_TeleportGates_Ck_teleportOutput
import Definitions.Def_TeleportGates_Ck_pauliFrame

namespace TeleportGates.Ck

open QAlgorithms

/-- **Teleportation of n qubits through `|Ψⁿ⟩`.**
Gottesman, Chuang, *Quantum teleportation is a universal computational primitive*,
arXiv:quant-ph/9908010v1, §I, unnumbered, p. 1: "We simply reverse the
appropriate Pauli operator to reconstruct |α⟩, as shown in Fig. 1. Replication of this circuit
allows teleportation of multiple qubits." §II, p. 2: "Let |Ψn⟩ be the 2n-(encoded) qubit Bell
state (|00⟩ + |11⟩)⊗n (normalizations suppressed for clarity), rearranged so that the first n
labels represent half of the EPR pairs (the upper qubits), and the last n the other half (the
lower qubits)."

For every `n`, every vector `ψ` of `n` qubits and every outcome strings `x z`, Bell-measuring
input qubit `i` against upper qubit `i` of `|Ψⁿ⟩` for each `i` leaves the lower register in
`2^{−n} R_{xz} ψ` with `R_{xz} = ⊗ᵢ X^{xᵢ} Z^{zᵢ}`, and the outcome has probability `‖ψ‖²/4ⁿ`.

**Formalization Note.** The factor `2^{−n} = (1/√2)ⁿ·(1/√2)ⁿ` comes from the normalized Bell
vectors and EPR pairs. `ψ` is any vector; `n = 0` is allowed (both sides are then scalars). -/
theorem teleport_n_qubits (n : ℕ) (ψ : EuclideanSpace ℂ (Qubits n)) (x z : Qubits n) :
    teleportOutput (bellVec n x z) ψ (eprState n) = ((2 : ℂ) ^ n)⁻¹ • act (pauliFrame n x z) ψ ∧
      ‖teleportOutput (bellVec n x z) ψ (eprState n)‖ ^ 2 = ‖ψ‖ ^ 2 / 4 ^ n := by sorry

end TeleportGates.Ck
