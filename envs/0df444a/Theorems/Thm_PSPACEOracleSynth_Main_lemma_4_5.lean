-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_lemma_4_5
-- name    : PSPACEOracleSynth.Main.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:23.611002+00:00
-- url     : https://prove2.me/theorems/cd033da7-8ee1-403c-ac80-bd52e63b20f8
-- title:
--   Lemma 4.5 — projective membership of $\mathcal U$ gives clean membership of $\mathcal U\otimes\mathcal U^\dagger$
-- statement:
--   Let $L$ be a classical oracle. If $\mathcal U\in\mathsf{projUnitaryP}^L$, then $\mathcal U\otimes\mathcal U^\dagger\in\mathsf{unitaryP}^L$, and if $\mathcal U\in\mathsf{projUnitaryPSPACE}^L$, then $\mathcal U\otimes\mathcal U^\dagger\in\mathsf{unitaryPSPACE}^L$.
--
--   With Lemma 4.6 this reduces the projective case of Theorem 1.1 to the clean case.
--
--   **Formalization Note.** $\mathcal U\otimes\mathcal U^\dagger$ is `tensorAdj U` (member $U_n\otimes U_n^\dagger$ on $2n$ qubits, identities on odd numbers of qubits); the clean classes are the published `unitaryP (emb L)`, `unitaryPSPACE (emb L)`.
--
--   Differences from the source:
--   - encoding: unitary languages (U_n)_{n≥1}, families (C_{n,m})_{n,m≥1} → published ULang indexed by n ∈ ℕ (U_0 a 1×1 phase); the classes quantify all n, l ∈ ℕ; reason: the paper identifies its classes with those of [KT26] (p. 10), which are the published definitions; the extra members are handled by the same arguments (U_0 is a phase computable in PSPACE^A, precision 2^0 follows from 2^{-1})
--   - encoding: clean classes: unitary circuits whose oracle gates are O_A (Definition 2.3) → published KT clean classes, whose circuits may also use O_A^*, O_A^†, O_A^T and controlled queries; the projective classes allow only plain O_A; reason: p. 10: the adjoint, transpose and conjugate of O_A are O_A, and a controlled query is simulated exactly with one ancilla, so the clean classes are the same
--   - encoding: classical oracle A ⊆ {0,1}*, language K → A : Str → Bool; K : Set Str used through langOracle K and the unitary embedding emb; reason: Lean convention; same oracles
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), §4.3, Lemma 4.5, p. 28

import Mathlib
import Definitions.Def_KTUnitary_Synth_emb
import Definitions.Def_KTUnitary_Synth_unitaryP
import Definitions.Def_KTUnitary_Synth_unitaryPSPACE
import Definitions.Def_PSPACEOracleSynth_Main_Dilation

open QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth

namespace PSPACEOracleSynth.Main

/-- **Lemma 4.5**, Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*, STOC 2027 submission
#1740, p. 28. Let `L` be a classical oracle. If `U ∈ projUnitaryP^L`, then
`U ⊗ U† ∈ unitaryP^L`, and if `U ∈ projUnitaryPSPACE^L`, then `U ⊗ U† ∈ unitaryPSPACE^L`. -/
theorem lemma_4_5 (L : Oracle) :
    (∀ U : ULang, U ∈ projUnitaryP L → tensorAdj U ∈ unitaryP (emb L)) ∧
    (∀ U : ULang, U ∈ projUnitaryPSPACE L → tensorAdj U ∈ unitaryPSPACE (emb L)) := by sorry

end PSPACEOracleSynth.Main
