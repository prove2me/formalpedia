-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_lemma_2_6_i
-- name    : PSPACEOracleSynth.Main.lemma_2_6_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:06.910008+00:00
-- url     : https://prove2.me/theorems/592614e3-ad57-4958-b64c-550cd5528cb4
-- title:
--   Lemma 2.6 (i) — $\mathsf{PSPACE}^{\mathsf{PSPACE}^A}=\mathsf{PSPACE}^A$
-- statement:
--   Relative to every classical oracle $A$,
--   $$\mathsf{PSPACE}^{\mathsf{PSPACE}^A}=\mathsf{PSPACE}^A,$$
--   where $\mathsf{PSPACE}^{\mathsf{PSPACE}^A}=\bigcup_{L\in\mathsf{PSPACE}^A}\mathsf{PSPACE}^L$ and the query tape counts toward the space bound.
--
--   The main theorem uses it to show that a unitary in $\mathsf{unitaryP}^L$ with $L\in\mathsf{PSPACE}^A$ has entries computable in polynomial space relative to $A$.
--
--   **Formalization Note.** $\mathsf{PSPACE}^O$ is the published `QAdvFew.PoQOracle.PSPACE O` (deterministic oracle Turing machines, space including the query tape); a language $L$ is used as the oracle `langOracle L`.
--
--   Differences from the source:
--   - encoding: PSPACE^{PSPACE^A} → ⋃_{L ∈ PSPACE^A} PSPACE^L; reason: the class of languages decidable in polynomial space with some oracle in PSPACE^A
--   - encoding: classical oracle A ⊆ {0,1}*, language L ∈ PSPACE^A used as an oracle → A : Str → Bool; L : Set Str used through langOracle L; reason: Lean convention; same oracles
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), §2.3, Lemma 2.6 (i), p. 11

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_PSPACE
import Definitions.Def_PSPACEOracleSynth_Main_Oracles

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace PSPACEOracleSynth.Main

/-- **Lemma 2.6 (i)**, Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*, STOC 2027
submission #1740, p. 11. Relative to every classical oracle `A`,
`PSPACE^{PSPACE^A} = PSPACE^A`: a language is decided in polynomial space (query tape counted)
with an oracle in `PSPACE^A` if and only if it is in `PSPACE^A`. -/
theorem lemma_2_6_i (A : Oracle) :
    (⋃ L ∈ PSPACE A, PSPACE (langOracle L)) = PSPACE A := by sorry

end PSPACEOracleSynth.Main
