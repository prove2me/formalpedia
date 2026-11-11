-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_lemma_4_6
-- name    : PSPACEOracleSynth.Main.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:21.582211+00:00
-- url     : https://prove2.me/theorems/c61827ee-60f3-4988-8de4-fa45020a2c1a
-- title:
--   Lemma 4.6 — clean membership of $\mathcal U\otimes\mathcal U^\dagger$ gives projective membership of $\mathcal U$
-- statement:
--   Let $L$ be a classical oracle. If $\mathcal U\otimes\mathcal U^\dagger\in\mathsf{unitaryP}^L$, then $\mathcal U\in\mathsf{projUnitaryP}^L$, and if $\mathcal U\otimes\mathcal U^\dagger\in\mathsf{unitaryPSPACE}^L$, then $\mathcal U\in\mathsf{projUnitaryPSPACE}^L$.
--
--   With Lemma 4.5 this reduces the projective case of Theorem 1.1 to the clean case.
--
--   **Formalization Note.** As in Lemma 4.5. The published clean classes allow controlled oracle queries while the projective classes allow only plain $O_L$ gates; by the simulation on p. 10 this does not change the classes.
--
--   Differences from the source:
--   - encoding: unitary languages (U_n)_{n≥1}, families (C_{n,m})_{n,m≥1} → published ULang indexed by n ∈ ℕ (U_0 a 1×1 phase); the classes quantify all n, l ∈ ℕ; reason: the paper identifies its classes with those of [KT26] (p. 10), which are the published definitions; the extra members are handled by the same arguments (U_0 is a phase computable in PSPACE^A, precision 2^0 follows from 2^{-1})
--   - encoding: clean classes: unitary circuits whose oracle gates are O_A (Definition 2.3) → published KT clean classes, whose circuits may also use O_A^*, O_A^†, O_A^T and controlled queries; the projective classes allow only plain O_A; reason: p. 10: the adjoint, transpose and conjugate of O_A are O_A, and a controlled query is simulated exactly with one ancilla, so the clean classes are the same
--   - encoding: classical oracle A ⊆ {0,1}*, language K → A : Str → Bool; K : Set Str used through langOracle K and the unitary embedding emb; reason: Lean convention; same oracles
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), §4.3, Lemma 4.6, p. 28

import Mathlib
import Definitions.Def_KTUnitary_Synth_emb
import Definitions.Def_KTUnitary_Synth_unitaryP
import Definitions.Def_KTUnitary_Synth_unitaryPSPACE
import Definitions.Def_PSPACEOracleSynth_Main_Dilation

open QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth

namespace PSPACEOracleSynth.Main

/-- **Lemma 4.6**, Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*, STOC 2027 submission
#1740, p. 28. Let `L` be a classical oracle. If `U ⊗ U† ∈ unitaryP^L`, then
`U ∈ projUnitaryP^L`, and if `U ⊗ U† ∈ unitaryPSPACE^L`, then `U ∈ projUnitaryPSPACE^L`. -/
theorem lemma_4_6 (L : Oracle) :
    (∀ U : ULang, tensorAdj U ∈ unitaryP (emb L) → U ∈ projUnitaryP L) ∧
    (∀ U : ULang, tensorAdj U ∈ unitaryPSPACE (emb L) → U ∈ projUnitaryPSPACE L) := by sorry

end PSPACEOracleSynth.Main
