-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_theorem_1_1
-- name    : PSPACEOracleSynth.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:43.635201+00:00
-- url     : https://prove2.me/theorems/a546e488-10d2-4fd6-ba84-71b480adefb6
-- title:
--   Theorem 1.1 (Main theorem) — $\mathsf{unitaryPSPACE}^A=\bigcup_{L\in\mathsf{PSPACE}^A}\mathsf{unitaryP}^L$, clean and projective, attained by every $\mathsf{PSPACE}^A$-complete $K$
-- statement:
--   For every classical oracle $A$,
--   $$\mathsf{unitaryPSPACE}^A=\bigcup_{L\in\mathsf{PSPACE}^A}\mathsf{unitaryP}^L,\qquad \mathsf{projUnitaryPSPACE}^A=\bigcup_{L\in\mathsf{PSPACE}^A}\mathsf{projUnitaryP}^L.$$
--   Moreover, if a language $K$ is $\mathsf{PSPACE}^A$-complete under polynomial-time many-one reductions computed without access to $A$, then
--   $$\mathsf{unitaryPSPACE}^A=\mathsf{unitaryP}^K\qquad\text{and}\qquad\mathsf{projUnitaryPSPACE}^A=\mathsf{projUnitaryP}^K.$$
--
--   Every unitary language implementable by polynomial-space-uniform circuits (with oracle $A$) is thus implementable by polynomial-time-uniform circuits with one fixed oracle, any $\mathsf{PSPACE}^A$-complete language (TQBF when $A=\emptyset$), for all sizes and all exponentially small precisions; the same holds for the projective classes, where the global phase does not count.
--
--   **Formalization Note.** The clean classes are the published `KTUnitary.Synth.unitaryP`/`unitaryPSPACE` applied to the unitary embedding `emb` of the oracle; the projective classes are `projUnitaryP`/`projUnitaryPSPACE` (definition `Dilation`). $\mathsf{PSPACE}^A$ is the published `PSPACE A`, and completeness is `IsPSPACECompleteRel` (oracle-free polynomial-time reductions).
--
--   Differences from the source:
--   - encoding: unitary languages (U_n)_{n≥1}, families (C_{n,m})_{n,m≥1} → published ULang indexed by n ∈ ℕ (U_0 a 1×1 phase); the classes quantify all n, l ∈ ℕ; reason: the paper identifies its classes with those of [KT26] (p. 10), which are the published definitions; the extra members are handled by the same arguments (U_0 is a phase computable in PSPACE^A, precision 2^0 follows from 2^{-1})
--   - encoding: clean classes: unitary circuits whose oracle gates are O_A (Definition 2.3) → published KT clean classes, whose circuits may also use O_A^*, O_A^†, O_A^T and controlled queries; the projective classes allow only plain O_A; reason: p. 10: the adjoint, transpose and conjugate of O_A are O_A, and a controlled query is simulated exactly with one ancilla, so the clean classes are the same
--   - encoding: classical oracle A ⊆ {0,1}*, language K → A : Str → Bool; K : Set Str used through langOracle K and the unitary embedding emb; reason: Lean convention; same oracles
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), §1, Theorem 1.1, p. 3 (proof §4.3, pp. 28–29)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_PSPACE
import Definitions.Def_KTUnitary_Synth_emb
import Definitions.Def_KTUnitary_Synth_unitaryP
import Definitions.Def_KTUnitary_Synth_unitaryPSPACE
import Definitions.Def_PSPACEOracleSynth_Main_Oracles
import Definitions.Def_PSPACEOracleSynth_Main_Dilation

open QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth

namespace PSPACEOracleSynth.Main

/-- **Theorem 1.1 (Main theorem)**, Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*,
STOC 2027 submission #1740, p. 3 (proof §4.3, pp. 28–29). For every classical oracle `A`,
`unitaryPSPACE^A = ⋃_{L ∈ PSPACE^A} unitaryP^L` and
`projUnitaryPSPACE^A = ⋃_{L ∈ PSPACE^A} projUnitaryP^L`. Moreover, if a language `K` is
`PSPACE^A`-complete under polynomial-time many-one reductions computed without access to `A`, then
`unitaryPSPACE^A = unitaryP^K` and `projUnitaryPSPACE^A = projUnitaryP^K`.

The clean classes are the published `KTUnitary.Synth.unitaryP`/`unitaryPSPACE` applied to the
unitary embedding `emb` of the oracle; the projective classes are `projUnitaryP`/
`projUnitaryPSPACE`. -/
theorem theorem_1_1 (A : Oracle) :
    unitaryPSPACE (emb A) = (⋃ L ∈ PSPACE A, unitaryP (emb (langOracle L))) ∧
    projUnitaryPSPACE A = (⋃ L ∈ PSPACE A, projUnitaryP (langOracle L)) ∧
    ∀ K : Set Str, IsPSPACECompleteRel A K →
      unitaryPSPACE (emb A) = unitaryP (emb (langOracle K)) ∧
      projUnitaryPSPACE A = projUnitaryP (langOracle K) := by sorry

end PSPACEOracleSynth.Main
