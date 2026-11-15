-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_ReverseCompiler_compileVerifier_acceptanceOperator
-- name    : QMAPerfectCompleteness.Main.ReverseCompiler.compileVerifier_acceptanceOperator
-- status  : Proved
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:43:30.215583+00:00
-- url     : https://prove2.me/theorems/509b5b3a-9a8d-483e-bf8c-9d96f249734b
-- title:
--   Exact acceptance preservation by the HT-to-HP compiler
-- statement:
--   For every Hadamard–Toffoli verifier V, replacing each Toffoli by the literal seventeen-gate H/controlled-P circuit preserves its acceptance operator:
--
--   $$
--   E_{\operatorname{HPcompile}(V)}=E_V.
--   $$
--
--   The compiler introduces no extra wires and leaves proof, ancilla, and output registers unchanged. The identity therefore preserves the acceptance probability of every proof and supplies the exact gate conversion used in the reverse class inclusion.
-- source:
--   Auxiliary formalization source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/ReverseCompiler.lean:71–74. Paper context: Sabee Grewal and Dorian Rudolph, QMA has perfect completeness, user-provided main.tex. Auxiliary exact reverse gate-compilation identity for the reverse inclusion in Theorem 1.1.

/- Generated from Solutions.ReverseCompiler by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_HPToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_ReverseCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



/-! Exact HT-to-HP compilation without additional wires. Each Toffoli is replaced by
its literal seventeen-gate H/controlled-P synthesis. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.ReverseCompiler
end QMAPerfectCompleteness.Main.ReverseCompiler
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.ReverseCompiler
open HPToffoli ReversibleGadgets

theorem QMAPerfectCompleteness.Main.ReverseCompiler.compileVerifier_acceptanceOperator (V : Verifier gatesHT) :
    (compileVerifier V).acceptanceOperator = V.acceptanceOperator := by sorry
