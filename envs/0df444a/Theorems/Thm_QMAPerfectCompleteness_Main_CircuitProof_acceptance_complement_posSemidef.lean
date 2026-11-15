-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_CircuitProof_acceptance_complement_posSemidef
-- name    : QMAPerfectCompleteness.Main.CircuitProof.acceptance_complement_posSemidef
-- status  : Proved
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:44:07.342452+00:00
-- url     : https://prove2.me/theorems/7981741a-0926-46cf-90a7-0f088d4daed4
-- title:
--   Positivity of the complementary acceptance effect
-- statement:
--   For every verifier V over any gate set, I−E_V is positive semidefinite, where E_V is its acceptance operator. Thus E_V is bounded above by the identity.
--
--   $$
--   I-E_V\succeq0.
--   $$
--
--   The operator bound is used in the spectral witness and acceptance-probability estimates.
-- source:
--   Local source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CircuitUnitary.lean:126-154; paper: QMA has perfect completeness, Sabee Grewal and Dorian Rudolph, user-provided main.tex.

/- Generated from Solutions.CircuitUnitary by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates



open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CircuitProof
end QMAPerfectCompleteness.Main.CircuitProof
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CircuitProof

























open scoped ComplexOrder

theorem QMAPerfectCompleteness.Main.CircuitProof.acceptance_complement_posSemidef {G : GateSet} (V : Verifier G) :
    (1 - V.acceptanceOperator).PosSemidef := by sorry
