-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_tm2_to_boolean_stacks
-- name    : QuantumMaxCutEnergy.tm2_to_boolean_stacks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T17:42:31.355119+00:00
-- url     : https://prove2.me/theorems/e2e45b22-7503-4b55-8d3b-2e418548371f
-- title:
--   Boolean-stack simulation of a finite-alphabet TM2 machine on the campaign encodings
-- statement:
--   Let $\alpha$ be an encoded input type with encoding $e_\alpha$, and let $f:\alpha\to\mathbb{Q}_{\ge0}$ admit a polynomial-time certificate on the campaign's canonical output encoding in Mathlib's multi-tape model `Turing.TM2ComputableInPolyTime`, whose stack alphabets are arbitrary finite types. Then $f$ is computed, in polynomial time, by a program of the library's Boolean-stack language `PolyProgram` that keeps the same input and output encodings.
--
--   In words: a finite-alphabet multi-tape machine with a polynomial step bound can be simulated, step for step with polynomial overhead, by a machine all of whose stacks are Boolean. Each symbol of a finite stack alphabet is written as a fixed block of bits, using an injection into $\{0,1\}^{b}$ for a suitable $b$; a simulated step then pops one constant-size block from each of the finitely many stacks that the instruction touches and pushes the blocks prescribed by the simulated transition. Constant overhead per simulated step preserves polynomial time, and the input and output tapes carry lists of bits in the campaign encodings already, so no re-encoding is needed here.
--
--   This isolates the machine-model simulation from the output-frame conversion, which is the separate lemma `QuantumMaxCutEnergy.ratio_frame_recode`.
-- source:
--   Not a quoted paper result. Simulation direction missing from Mathlib 0df444a (`Turing.TM2ComputableInPolyTime.comp` is a `proof_wanted` there) and from the campaign runtime module, which supplies only `OAI.MetricKMedian.Binary.PolyProgram.stock` (program to machine). Needed, together with the ratio-frame recoding, for `QuantumMaxCutEnergy.exists_polyProgram_of_tm2InPolyTime`, hence for the polynomial-time certificates of Anshu--Gosset--Morenz, TQC 2020, Theorem 3 (https://doi.org/10.4230/LIPIcs.TQC.2020.7).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.tm2_to_boolean_stacks
    {α : Type} (ea : α → List Bool) (f : α → ℚ≥0)
    (h : Nonempty (Turing.TM2ComputableInPolyTime ea QuantumMaxCutEnergy.encodeValue f)) :
    Nonempty (OAI.MetricKMedian.Binary.PolyProgram ea QuantumMaxCutEnergy.encodeValue f) := by sorry
