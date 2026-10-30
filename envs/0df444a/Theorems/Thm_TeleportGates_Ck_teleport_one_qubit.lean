-- Prove2me | Theorems.Thm_TeleportGates_Ck_teleport_one_qubit
-- name    : TeleportGates.Ck.teleport_one_qubit
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:15:13.906637+00:00
-- url     : https://prove2.me/theorems/2ec74730-977f-4af2-957c-e83a4d473b47
-- title:
--   Single-qubit teleportation: outcome $xz$ leaves $\tfrac12 X^xZ^z\alpha$, each with probability $\|\alpha\|^2/4$
-- statement:
--   Let $\alpha\in\mathbb C^2$ and let $|\Psi\rangle=(|00\rangle+|11\rangle)/\sqrt2$. Measure $\alpha$ together with the upper qubit of $|\Psi\rangle$ in the Bell basis $\beta_{xz}=(|0x\rangle+(-1)^z|1\bar x\rangle)/\sqrt2$. For every outcome $(x,z)$ the (unnormalized) state left on the lower qubit is
--
--   $$(\langle\beta_{xz}|\otimes I)(\alpha\otimes\Psi)=\tfrac12\,X^xZ^z\alpha,$$
--
--   and the outcome has probability
--
--   $$\bigl\|(\langle\beta_{xz}|\otimes I)(\alpha\otimes\Psi)\bigr\|^2=\frac{\|\alpha\|^2}{4}.$$
--
--   So the four outcomes are equally likely, the output is the input up to the Pauli $I$, $Z$, $X$ or $XZ=-iY$, and outcome $00$ gives the identity. This is the teleportation step that the paper replicates and then modifies.
--
--   Differences from the source:
--   - encoding: Bell vectors |0x⟩ + (−1)^z|1x̄⟩ and EPR pairs |00⟩ + |11⟩ with normalizations suppressed (p. 2) → normalized Bell vectors and EPR pairs (each factor 1/√2); the post-measurement state is the unnormalized contraction, so the identity carries an explicit constant; reason: fixes the constants; the paper's |ψout⟩ is this vector up to normalization
--   - reading: |α⟩ and one qubit of |Ψ⟩ are measured together in the Bell basis |0x⟩ + (−1)^z|1x̄⟩ (p. 1) → in |0x⟩ + (−1)^z|1x̄⟩ the first ket is the teleported qubit, the second the EPR half; reason: the paper names |α⟩ first; swapping the factors changes the Pauli frame by a reordering and a phase
--   - reading: R_xz, an operator in C1 which depends on the outcomes xz (not written out); for one qubit 'X, Y, or Z', 00 the identity → the explicit R_xz = ⊗_i X^{x_i} Z^{z_i} (Z first), with XZ = −iY for x_i = z_i = 1; reason: this is the frame the p. 1 Bell basis (first ket = teleported qubit) and |00⟩ + |11⟩ give, checked by hand and by a proved sanity check for n = 1; the paper's 'Y' is −iY up to a global phase
--   - generalization: an input state |α⟩ (a unit vector) → |α⟩ any vector of the input register; reason: the identities are linear in the input; for a unit vector they are the paper's statement
-- source:
--   Gottesman, Chuang, Quantum teleportation is a universal computational primitive, arXiv:quant-ph/9908010v1, §I, unnumbered, p. 1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_TeleportGates_Ck_bell1
import Definitions.Def_TeleportGates_Ck_epr1
import Definitions.Def_TeleportGates_Ck_teleportOutput

namespace TeleportGates.Ck

open QAlgorithms

/-- **Single-qubit teleportation.**
Gottesman, Chuang, *Quantum teleportation is a universal computational primitive*,
arXiv:quant-ph/9908010v1, §I, unnumbered, p. 1: "a single qubit state
|α⟩ = a|0⟩ + b|1⟩ is prepared, along with an EPR state |Ψ⟩ = (|00⟩ + |11⟩)/√2, then |α⟩ and one
qubit of |Ψ⟩ are measured together in the Bell basis |0x⟩ + (−1)^z|1x̄⟩ (where x, z = {0, 1}, and
x̄ = 1 − x), giving a (uniformly distributed) random two-bit classical result which is xz. The
output qubit is then in the initial state |α⟩, but with an additional single-qubit Pauli
operation X, Y, or Z applied to it, with the random variable xz determining which Pauli operator
it is (with 00 corresponding to the identity)."

For every outcome `(x, z)` and every vector `α`, projecting the first two qubits of `α ⊗ Ψ` onto
`β_{xz}` leaves the third qubit in `½ X^x Z^z α`, and the outcome has probability
`‖α‖²/4` (`1/4` for a unit `α`).

**Formalization Note.** `teleportOutput (bell1 x z) α epr1` is the unnormalized post-measurement
state; the factor `½ = (1/√2)·(1/√2)` comes from the normalized Bell vector and EPR pair. The
Pauli is `X^x Z^z` (Z first); for `x = z = 1` it is `XZ = −iY`, the paper's "Y" up to a phase.
`α` is any vector, not only a unit vector. -/
theorem teleport_one_qubit (x z : Bool) (α : EuclideanSpace ℂ Bool) :
    teleportOutput (bell1 x z) α epr1 =
        (1 / 2 : ℂ) • act ((if x then pauliX else 1) * (if z then pauliZ else 1)) α ∧
      ‖teleportOutput (bell1 x z) α epr1‖ ^ 2 = ‖α‖ ^ 2 / 4 := by sorry

end TeleportGates.Ck
