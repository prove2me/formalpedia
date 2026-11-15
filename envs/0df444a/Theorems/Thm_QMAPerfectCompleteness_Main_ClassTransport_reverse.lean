-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_ClassTransport_reverse
-- name    : QMAPerfectCompleteness.Main.ClassTransport.reverse
-- status  : Proved
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:44:21.963057+00:00
-- url     : https://prove2.me/theorems/da379395-6366-47a3-8696-8bcbdc9ecd26
-- title:
--   Exact compiler and two-copy pipeline for the reverse inclusion
-- statement:
--   Assume the HP-to-G₂, two-copy G₂ repetition, G₂-to-HT, and HT-to-HP code compilers each preserve polynomial-time generation on valid verifier codes. Then
--
--   $$
--   \operatorname{QMA}_1^{HT}\subseteq\operatorname{QMA}.
--   $$
--
--   Starting from HT completeness one and soundness 1/2, the exact pipeline HT→HP→G₂→two-copy repetition→HT→HP reaches completeness one and soundness 1/4. Weakening these thresholds gives the 2/3 and 1/3 parameters of QMA. Each runtime premise concerns valid-code generators on every input, rather than arbitrary malformed circuit strings.
-- source:
--   Auxiliary formalization source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/ClassPipeline.lean:52–68. Paper context: Sabee Grewal and Dorian Rudolph, QMA has perfect completeness, user-provided main.tex. Auxiliary exact class-assembly argument for the reverse inclusion of Theorem 1.1.

/- Generated from Solutions.ClassPipeline by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClassTransport
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HPToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_HTEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_HTPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReverseCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



/-! The exact gate-choice and constant-amplification pipeline, with only the specific
code-generator runtime obligations as explicit hypotheses. -/
namespace QMAPerfectCompleteness.Main.ClassTransport
end QMAPerfectCompleteness.Main.ClassTransport
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.ClassTransport

theorem QMAPerfectCompleteness.Main.ClassTransport.reverse
    (hD : UniformOnVerifierCodes gatesHP DyadicCompiler.executableCompile)
    (hR : UniformOnVerifierCodes gatesG2 (Repetition.Encoding.executableCompile 2))
    (hHT : UniformOnVerifierCodes gatesG2 HTCompiler.executableCompile)
    (hHP : UniformOnVerifierCodes gatesHT ReverseCompiler.executableCompile) :
    QMA1 gatesHT ⊆ QMA := by sorry
