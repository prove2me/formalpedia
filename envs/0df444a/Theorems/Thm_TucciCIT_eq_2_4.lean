-- Prove2me | Theorems.Thm_TucciCIT_eq_2_4
-- name    : TucciCIT.eq_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:29:54.923251+00:00
-- url     : https://prove2.me/theorems/a528eea9-0dce-4de6-bb6d-0b1d6b4ba536
-- title:
--   Eq. (2.4) — $E_F(\psi) = S(\psi\psi^\dagger)$
-- statement:
--   Let $\psi$ be the rectangular matrix of amplitudes $\psi_{xy} = \langle x, y|\psi\rangle$ of a vector $|\psi\rangle \in \mathcal H_x \otimes \mathcal H_y$. Then
--
--   $$
--   E_F(\psi) = S(\psi\psi^\dagger),
--   $$
--
--   the von Neumann entropy (bits) of the $S_x \times S_x$ matrix $\psi\psi^\dagger$: the reduced density matrix $\operatorname{tr}_y |\psi\rangle\langle\psi|$ is $\psi\psi^\dagger$.
--
--   This identity turns every entanglement-of-formation computation into a computation on a matrix of size $N_x$.
--
--   Differences from the source:
--   - generalization: |ψ⟩ a (normalized) bipartite pure state → any amplitude matrix ψ; reason: the identity tr_y|ψ⟩⟨ψ| = ψψ† holds entrywise for every ψ; it specializes to unit ψ
--   - encoding: S = von Neumann entropy, logarithms base 2 (eqs. (2.9), (4.11)) → QAlgorithms.vnEntropy (−Re Tr f(ρ), f(t) = t log₂ t, 0 log 0 = 0) of redistributionMarginal partial traces; reason: Lean convention; same values
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, eq. (2.4), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_TucciCIT_entanglementOfFormation

open QAlgorithms
open scoped Matrix

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, eq. (2.4), p.3 (PDF p.3): "Let ψ be the rectangular matrix with
entries ψxy = ⟨x, y|ψ⟩. … Thus, EF(ψxy) = S(ψψ†)."

For every amplitude matrix `ψ : Matrix X Y ℂ`, the pure-state entanglement of formation
`EF(ψ) = S[tr_y |ψ⟩⟨ψ|]` (eq. (2.1)) equals the von Neumann entropy (bits) of the `X × X`
matrix `ψψ†`.

**Formalization Note.** No normalization is assumed: the reduced matrix `tr_y |ψ⟩⟨ψ|` equals
`ψψ†` entrywise for every `ψ`. -/
theorem eq_2_4 {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    (ψ : Matrix X Y ℂ) :
    entanglementOfFormation ψ = vnEntropy (ψ * ψᴴ) := by sorry

end TucciCIT
