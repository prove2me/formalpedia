-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_Supplement_theorem_7_7
-- name    : PSPACEOracleSynth.Main.Supplement.theorem_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T14:44:25.819191+00:00
-- url     : https://prove2.me/theorems/033ea799-e70f-4a2e-bdc2-366e70f36af3
-- title:
--   Theorem 7.7 — Every size-computable interactive channel-model synthesis problem has a polynomial-space implementation.
-- statement:
--   Every size-computable interactive synthesis problem satisfies
--
--   $$U\in\mathrm{unitaryQIP}^{\diamond}_{1,1/2}\quad\Longrightarrow\quad U\in\mathrm{unitaryPSPACE}^{\diamond}.$$
--
--   The conclusion requires one completion at each instance and precision before any entangled test input is chosen. This is the full channel-model converse used with Theorems 6.2 and 7.1 in Theorem 1.5.
--
--   Differences from the source:
--   - encoding: finite qubit registers and normalized states → Bits n, UnitKet and density-matrix predicates, including n=0; reason: basis labels and explicit state predicates change no instance
--   - encoding: real full diamond norm over pure reference-entangled inputs → an extended nonnegative real supremum over all pure inputs and finite qubit references; reason: bounds are identical and the supremum has no empty or unbounded real default
--   - encoding: oracle-free generators with named input/output wires and unary precision → published TimeUniform and SpaceUniform on tuple codes and canonical current wire labels; reason: renaming live wires and decoding interface counts preserve all circuit families and their polynomial resources
--   - encoding: verifier rounds over G including T-dagger → published general-circuit verifier rounds over H,T,CNOT, with T-dagger compiled as seven T gates; reason: the compilation is exact and has constant overhead; prover channels and persistent memory are unrestricted
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Theorem 7.7, p. 42

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Interaction

open QAlgorithms QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
open scoped Matrix ComplexOrder Kronecker ENNReal
noncomputable section

namespace PSPACEOracleSynth.Main.Supplement

theorem theorem_7_7 (U : SynthProblem) (hsize : SizeComputable U)
    (hU : U ∈ channelQIP) : U ∈ channelPSPACE := by sorry

end PSPACEOracleSynth.Main.Supplement
