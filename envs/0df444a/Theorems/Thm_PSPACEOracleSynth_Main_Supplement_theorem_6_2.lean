-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_Supplement_theorem_6_2
-- name    : PSPACEOracleSynth.Main.Supplement.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:35:09.064448+00:00
-- url     : https://prove2.me/theorems/50a0b77d-06ec-4a80-8b44-74d9fdd419a6
-- title:
--   Theorem 6.2 — Every size-computable channel-model polynomial-space problem has a polynomial-time implementation with one PSPACE language as oracle.
-- statement:
--   Let $U$ be a size-computable problem in the channel-model class $\mathrm{unitaryPSPACE}^{\diamond}$. There is one classical language $B\in\mathrm{PSPACE}$ such that
--
--   $$U\in\mathrm{unitaryBQP}^{\diamond,B}.$$
--
--   The same oracle language serves every instance and precision of the problem; the classical circuit generator uses no oracle.
--
--   Differences from the source:
--   - encoding: finite qubit registers and normalized states → Bits n, UnitKet and density-matrix predicates, including n=0; reason: basis labels and explicit state predicates change no instance
--   - encoding: real full diamond norm over pure reference-entangled inputs → an extended nonnegative real supremum over all pure inputs and finite qubit references; reason: bounds are identical and the supremum has no empty or unbounded real default
--   - encoding: oracle-free generators with named input/output wires and unary precision → published TimeUniform and SpaceUniform on tuple codes and canonical current wire labels; reason: renaming live wires and decoding interface counts preserve all circuit families and their polynomial resources
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Theorem 6.2, p. 35

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Interaction

open QAlgorithms QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
open scoped Matrix ComplexOrder Kronecker ENNReal
noncomputable section

namespace PSPACEOracleSynth.Main.Supplement

theorem theorem_6_2 (U : SynthProblem) (hU : U ∈ channelPSPACE)
    (hsize : SizeComputable U) :
    ∃ B ∈ PSPACE (fun _ => false), U ∈ channelBQPO (langOracle B) := by sorry

end PSPACEOracleSynth.Main.Supplement
