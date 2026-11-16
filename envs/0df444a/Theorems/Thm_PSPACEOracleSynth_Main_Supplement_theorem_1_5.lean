-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_Supplement_theorem_1_5
-- name    : PSPACEOracleSynth.Main.Supplement.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:32:06.737524+00:00
-- url     : https://prove2.me/theorems/d215490f-4282-4260-b63b-f3f7e99eadd9
-- title:
--   Theorem 1.5 — Size-computable partial-isometry synthesis: polynomial space iff interactive synthesis with completeness one and threshold 1/2.
-- statement:
--   Let $U$ be any size-computable string-indexed partial-isometry synthesis problem. Then
--
--   $$U\in\mathrm{unitaryPSPACE}^{\diamond}\quad\Longleftrightarrow\quad U\in\mathrm{unitaryQIP}^{\diamond}_{1,1/2}.$$
--
--   The equivalence uses the channel model, covers every instance and every positive unary precision, and includes arbitrary partial supports. It is the paper's companion characterization of worst-case interactive synthesis.
--
--   Differences from the source:
--   - encoding: finite qubit registers and normalized states → Bits n, UnitKet and density-matrix predicates, including n=0; reason: basis labels and explicit state predicates change no instance
--   - encoding: real full diamond norm over pure reference-entangled inputs → an extended nonnegative real supremum over all pure inputs and finite qubit references; reason: bounds are identical and the supremum has no empty or unbounded real default
--   - encoding: oracle-free generators with named input/output wires and unary precision → published TimeUniform and SpaceUniform on tuple codes and canonical current wire labels; reason: renaming live wires and decoding interface counts preserve all circuit families and their polynomial resources
--   - encoding: verifier rounds over G including T-dagger → published general-circuit verifier rounds over H,T,CNOT, with T-dagger compiled as seven T gates; reason: the compilation is exact and has constant overhead; prover channels and persistent memory are unrestricted
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Theorem 1.5, p. 5

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Interaction

open QAlgorithms QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
open scoped Matrix ComplexOrder Kronecker ENNReal
noncomputable section

namespace PSPACEOracleSynth.Main.Supplement

theorem theorem_1_5 (U : SynthProblem) (hsize : SizeComputable U) :
    U ∈ channelPSPACE ↔ U ∈ channelQIP := by sorry

end PSPACEOracleSynth.Main.Supplement
