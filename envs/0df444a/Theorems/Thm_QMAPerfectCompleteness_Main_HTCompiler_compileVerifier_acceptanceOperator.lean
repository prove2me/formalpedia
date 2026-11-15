-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_HTCompiler_compileVerifier_acceptanceOperator
-- name    : QMAPerfectCompleteness.Main.HTCompiler.compileVerifier_acceptanceOperator
-- status  : Proved
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:42:37.470528+00:00
-- url     : https://prove2.me/theorems/a9760ef9-568d-4f48-8032-c2c7074162cf
-- title:
--   Exact acceptance preservation by the G₂-to-HT compiler
-- statement:
--   For every G₂ verifier V, the compiler using Hadamard and Toffoli gates and three shared clean ancillary wires has exactly the same proof-space acceptance operator:
--
--   $$
--   E_{\operatorname{HTcompile}(V)}=E_V.
--   $$
--
--   The source proof register is unchanged. Hence the equality preserves acceptance probabilities for every mixed proof, including proofs entangled across any decomposition of that register. It provides the semantic justification for exact gate synthesis after amplification.
-- source:
--   Auxiliary formalization source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/HTPreservation.lean:343–359. Paper context: Sabee Grewal and Dorian Rudolph, QMA has perfect completeness, user-provided main.tex. Auxiliary acceptance-preservation theorem for the exact Hadamard–Toffoli synthesis used in the proof of Theorem 1.1.

/- Generated from Solutions.HTPreservation by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_HTPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.HTCompiler
end QMAPerfectCompleteness.Main.HTCompiler
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.HTCompiler
open HadamardToffoli ReversibleGadgets

theorem QMAPerfectCompleteness.Main.HTCompiler.compileVerifier_acceptanceOperator (V : Verifier gatesG2) :
    (compileVerifier V).acceptanceOperator = V.acceptanceOperator := by sorry
