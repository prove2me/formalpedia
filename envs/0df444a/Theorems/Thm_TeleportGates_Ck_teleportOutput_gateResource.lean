-- Prove2me | Theorems.Thm_TeleportGates_Ck_teleportOutput_gateResource
-- name    : TeleportGates.Ck.teleportOutput_gateResource
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:15:16.000381+00:00
-- url     : https://prove2.me/theorems/37c1b257-309b-4cb0-83d5-644e522befb5
-- title:
--   Bell measurement commutes with $U$ on the lower register: $(\langle\beta|\otimes I)(\psi\otimes(I\otimes U)\Phi)=U(\langle\beta|\otimes I)(\psi\otimes\Phi)$
-- statement:
--   Let $\iota$ be a finite index set, $U$ any operator on $\mathbb C^\iota$, $\beta,\Phi\in\mathbb C^\iota\otimes\mathbb C^\iota$ and $\psi\in\mathbb C^\iota$. Then
--
--   $$(\langle\beta|\otimes I)\bigl(\psi\otimes(I\otimes U)\Phi\bigr)=U\,(\langle\beta|\otimes I)(\psi\otimes\Phi).$$
--
--   That is, applying $U$ to the lower register of the resource before the measurement of the input and upper registers is the same as applying it to the output afterwards. With $\Phi=|\Psi^n\rangle$ and $\beta$ a Bell outcome this turns the resource $|\Psi^n_U\rangle=(I\otimes U)|\Psi^n\rangle$ into $U$ applied to the teleported state.
--
--   Differences from the source:
--   - generalization: U a gate on the n lower qubits of |Ψn⟩, measured against Bell outcomes → every square matrix U on every finite index type ι, every vector β and every resource Φ; reason: the identity is linear algebra; at ι = Qubits n, β = bellVec n x z, Φ = eprState n, U unitary it is the paper's case
--   - generalization: an input state |ψ⟩ (a unit vector) → |ψ⟩ any vector of the input register; reason: the identities are linear in the input; for a unit vector they are the paper's statement
-- source:
--   Gottesman, Chuang, Quantum teleportation is a universal computational primitive, arXiv:quant-ph/9908010v1, §II, unnumbered, p. 2 ('(I ⊗ U)|Ψn⟩ … is U acting on the lower qubits of all the EPR pairs'); §I, p. 2 (the Bell measurement acts 'at a time which is before the cnot gate')

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_TeleportGates_Ck_gateResource
import Definitions.Def_TeleportGates_Ck_teleportOutput

namespace TeleportGates.Ck

open QAlgorithms

/-- **The Bell measurement commutes with `U` on the lower register.**
Gottesman, Chuang, *Quantum teleportation is a universal computational primitive*,
arXiv:quant-ph/9908010v1, §I, unnumbered, p. 2: "For each EPR pair, the
Bell basis measurement effectively introduces one of four random quantum operations (I, X, Y, Z)
to the other half of the involved EPR pair, at a time which is before the cnot gate." §II, p. 2:
"In other words, (I ⊗ U)|Ψn⟩ (where I is the identity on n qubits) is U acting on the lower
qubits of all the EPR pairs."

For every finite index type `ι`, every operator `U` on `ι`, every vector `β` (the measured
outcome), every input `ψ` and every resource state `Φ`, measuring the input and upper registers of
`ψ ⊗ (I ⊗ U)Φ` onto `β` gives `U` applied to the result of measuring `ψ ⊗ Φ`:
`(⟨β| ⊗ I)(ψ ⊗ (I ⊗ U)Φ) = U (⟨β| ⊗ I)(ψ ⊗ Φ)`.

**Formalization Note.** Stated for every square matrix `U`, every finite `ι`, every `β` and
`Φ`; the paper's case is `ι = Qubits n`, `β = bellVec n x z`, `Φ = eprState n`. -/
theorem teleportOutput_gateResource {ι : Type*} [Fintype ι] (β : EuclideanSpace ℂ (ι × ι))
    (ψ : EuclideanSpace ℂ ι) (Φ : EuclideanSpace ℂ (ι × ι)) (U : Matrix ι ι ℂ) :
    teleportOutput β ψ (gateResource U Φ) = act U (teleportOutput β ψ Φ) := by sorry

end TeleportGates.Ck
