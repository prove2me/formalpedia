-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_ClassTransport_transport
-- name    : QMAPerfectCompleteness.Main.ClassTransport.transport
-- status  : Proved
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:45:03.389073+00:00
-- url     : https://prove2.me/theorems/3f3fa559-26a2-4b41-940a-0a4f2e208451
-- title:
--   Transport of uniform QMA classes by a verifier compiler
-- statement:
--   Let a compiler from G-verifiers to H-verifiers have a code map agreeing with verifier encodings and preserving polynomial-time generation on valid codes. If it maps completeness threshold c to c′ and soundness threshold s to s′, then QMAClass(G,c,s) is contained in QMAClass(H,c′,s′).
--
--   $$
--   \operatorname{QMAClass}(G,c,s)\subseteq\operatorname{QMAClass}(H,c^{\prime},s^{\prime}).
--   $$
--
--   This assembly principle combines concrete uniform generation with the semantic completeness and soundness bounds.
-- source:
--   Local source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/ClassTransport.lean:19-35; paper: QMA has perfect completeness, Sabee Grewal and Dorian Rudolph, user-provided main.tex.

/- Generated from Solutions.ClassTransport by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



/-! Class assembly needs only continuations of generators whose outputs are verifier codes.
No general polynomial-time composition theorem, nor a runtime specification on malformed
compiler inputs, is required by these reductions. The runtime hypotheses below remain explicit. -/
namespace QMAPerfectCompleteness.Main.ClassTransport
end QMAPerfectCompleteness.Main.ClassTransport
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.ClassTransport
open QAlgorithms.Complexity (Str PolyTimeComputable)

theorem QMAPerfectCompleteness.Main.ClassTransport.transport {G H : GateSet} {c s c' s' : ℝ}
    (compile : Verifier G → Verifier H) (code : Str → Str)
    (hcode : ∀ V, code V.encode = (compile V).encode)
    (htime : UniformOnVerifierCodes G code)
    (hyes : ∀ V, V.AcceptsSomeProof c → (compile V).AcceptsSomeProof c')
    (hno : ∀ V, V.AcceptsAllProofsAtMost s → (compile V).AcceptsAllProofsAtMost s') :
    QMAClass G c s ⊆ QMAClass H c' s' := by sorry
