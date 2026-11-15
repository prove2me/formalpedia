-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_Repetition_CircuitProof_acceptanceOperator_pi
-- name    : QMAPerfectCompleteness.Main.Repetition.CircuitProof.acceptanceOperator_pi
-- status  : Proved
-- author  : @Dorian Rudolph
-- created : 2026-11-14T16:43:00.012129+00:00
-- url     : https://prove2.me/theorems/6f56a36a-b7ad-431f-9fa9-825eddae64b1
-- title:
--   The physical repetition verifier has the tensor acceptance effect
-- statement:
--   Let V be a G₂ verifier and let n be any natural number. Run n copies on disjoint registers and compute the AND of their outputs with the literal reversible flag circuit. Under the proof-register regrouping bijection phi, the resulting acceptance operator is
--
--   $$
--   (E_{\operatorname{repeat}_n(V)})_{p,q}
--    =\left(\bigotimes_{i=0}^{n-1}E_V\right)_{\phi(p),\phi(q)}.
--   $$
--
--   The equality includes initialization of all copy ancillas and AND flags; n=0 uses the empty tensor product. It is an operator identity on the full proof space, so the later soundness bound applies to arbitrary entangled proofs.
-- source:
--   Auxiliary formalization source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RepetitionCircuit.lean:497–524. Paper context: Sabee Grewal and Dorian Rudolph, QMA has perfect completeness, user-provided main.tex. Auxiliary literal-circuit realization of the tensor acceptance effect used for constant-gap amplification in the proof of Theorem 1.1.

/- Generated from Solutions.RepetitionCircuit by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



open Matrix
open scoped Kronecker ComplexOrder

set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.Repetition.CircuitProof
end QMAPerfectCompleteness.Main.Repetition.CircuitProof
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.Repetition QMAPerfectCompleteness.Main.Repetition.CircuitProof
open Circuit ReversibleGadgets VerifierAnalysis








































/-! Generic finite tensor matrices on function-indexed copy registers. -/

theorem QMAPerfectCompleteness.Main.Repetition.CircuitProof.acceptanceOperator_pi (V : Verifier gatesG2) (n : ℕ) :
    (Circuit.verifier V n).acceptanceOperator =
      (piMatrix (fun _ : Fin n => V.acceptanceOperator)).submatrix (proofEquiv V n) (proofEquiv V n) := by sorry
