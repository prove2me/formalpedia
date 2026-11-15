-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_DyadicCompiler_compileVerifier_acceptanceOperator
-- name    : QMAPerfectCompleteness.Main.DyadicCompiler.compileVerifier_acceptanceOperator
-- status  : Proved
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:42:10.493911+00:00
-- url     : https://prove2.me/theorems/67e1250c-b1e7-4e27-9fc9-9225baa1de7f
-- title:
--   Exact acceptance effect of the real-simulation compiler
-- statement:
--   For every verifier V over H and controlled-P gates, let E_V be its acceptance operator and let R(E_V) denote the real block representation, embedded back into complex matrices. The G₂ compiler adds a simulation proof bit; under the proof-basis bijection phi, its acceptance operator is exactly
--
--   $$
--   (E_{V'})_{p,q}
--    =\bigl(R(E_V)\bigr)_{\phi(p),\phi(q)},
--   \qquad
--   R(A)=\begin{pmatrix}\operatorname{Re}A&-\operatorname{Im}A\\
--   \operatorname{Im}A&\operatorname{Re}A\end{pmatrix}.
--   $$
--
--   The circuit unitary also has an ancillary spectator factor, but that wire is initialized and ignored in readout, so it contributes no additional proof-space factor to the acceptance effect. The identity is the semantic core of exact completeness and soundness preservation in Lemma 3.1.
-- source:
--   Auxiliary formalization source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/DyadicCompiler.lean:629–664. Paper context: Sabee Grewal and Dorian Rudolph, QMA has perfect completeness, user-provided main.tex. Exact real-simulation acceptance identity supporting Lemma 3.1; auxiliary gate-list formalization of the paper's real simulation.

/- Generated from Solutions.DyadicCompiler by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.DyadicCompiler
end QMAPerfectCompleteness.Main.DyadicCompiler
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.DyadicCompiler
open GateCompilation

theorem QMAPerfectCompleteness.Main.DyadicCompiler.compileVerifier_acceptanceOperator (V : Verifier gatesHP) :
    (compileVerifier V).acceptanceOperator =
      (complexRealRep V.acceptanceOperator).submatrix (splitProof V.proofQubits) (splitProof V.proofQubits) := by sorry
