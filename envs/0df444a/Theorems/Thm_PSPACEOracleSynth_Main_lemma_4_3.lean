-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_lemma_4_3
-- name    : PSPACEOracleSynth.Main.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:09.651197+00:00
-- url     : https://prove2.me/theorems/13710482-3a7c-46a7-9643-8bcc87623830
-- title:
--   Lemma 4.3 — NOT, Toffoli and the $I/H/T/T^\dagger$ uniformly controlled gate are exact over $G$
-- statement:
--   The NOT gate, the Toffoli gate and the uniformly controlled gate with a two-bit control that applies $I,H,T,T^\dagger$ for the strings $00,01,10,11$ are implemented exactly over $G=\{H,T,T^\dagger,\mathrm{CNOT}\}$ with ancillas returned to zero.
--
--   That is, for each of the three gates $V$ (on $1$, $3$ and $3$ wires) there is a circuit $C$ over $G$, acting on the wires of $V$ followed by ancillas, with
--   $$C(|\psi\rangle|0^a\rangle)=(V|\psi\rangle)|0^a\rangle\qquad\text{for every }|\psi\rangle,$$
--   so $C$ is an extension of $V$ and the error is zero. This lets the construction use NOT, Toffoli and controlled gates freely while keeping every circuit over $G$.
--
--   **Formalization Note.** The circuits are published `UCircuit`s with no oracle gates whose explicit gates decode, under one encoding $f$ with an FPTEAS, exactly to $H$, $T$, $T^\dagger$ or CNOT (`OverG`, `OracleFree`); the gate acts on the first wires and the ancillas are the remaining ones. Since there are no oracle gates, the unitary does not depend on the oracle argument, which is quantified universally.
--
--   Differences from the source:
--   - encoding: implemented exactly over G with ancillas returned to zero → a UCircuit over G with no oracle gates whose unitary is an extension (IsExtension) of the gate, gate wires first and ancillas last; reason: the definition of exact implementation on the zero-ancilla subspace (p. 9) with error 0
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), §4.2, Lemma 4.3, p. 26 (proof p. 27)

import Mathlib
import Definitions.Def_KTUnitary_Synth_HasFPTEAS
import Definitions.Def_KTUnitary_Synth_UCircuit
import Definitions.Def_KTUnitary_Synth_IsExtension
import Definitions.Def_PSPACEOracleSynth_Main_GateSet

open QAlgorithms.Complexity KTUnitary.Synth

namespace PSPACEOracleSynth.Main

/-- **Lemma 4.3**, Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*, STOC 2027 submission
#1740, p. 26 (proof p. 27). The NOT gate, the Toffoli gate and the uniformly controlled gate with a
two-bit control that applies `I, H, T, T†` for the strings `00, 01, 10, 11` are implemented exactly
over `G` with ancillas returned to zero: for each there is a circuit over `G = {H, T, T†, CNOT}`
(no oracle gates; explicit gates encoded by an encoding `f` with an FPTEAS) on the gate's wires
followed by ancillas, whose unitary is an extension of the gate. -/
theorem lemma_4_3 :
    ∃ f : Str → ℝ, HasFPTEAS f ∧
      (∃ C : UCircuit, OverG f C ∧ OracleFree C ∧ ∃ h : 1 ≤ C.N,
        ∀ O : ULang, IsExtension h notGate (C.unitary f O)) ∧
      (∃ C : UCircuit, OverG f C ∧ OracleFree C ∧ ∃ h : 3 ≤ C.N,
        ∀ O : ULang, IsExtension h toffoliGate (C.unitary f O)) ∧
      (∃ C : UCircuit, OverG f C ∧ OracleFree C ∧ ∃ h : 3 ≤ C.N,
        ∀ O : ULang, IsExtension h ucIHTTGate (C.unitary f O)) := by sorry

end PSPACEOracleSynth.Main
