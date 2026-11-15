-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_BlockVerifierCoordinates_spectator_mask
-- name    : QMAPerfectCompleteness.Main.BlockVerifierCoordinates.spectator_mask
-- status  : Proved
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:44:11.321349+00:00
-- url     : https://prove2.me/theorems/32922abd-2214-4871-afd0-73f794ab0411
-- title:
--   Complement of the verifier register in the block layout
-- statement:
--   For any G₂ verifier V, workspace size w, and block basis strings x and y, agreement outside the embedded verifier wires is equivalent to agreement on the index, clock, flag, and workspace coordinates.
--
--   $$
--   x=y\text{ outside the verifier bank}\iff(x_{\rm index},x_{\rm clock},x_{\rm flag},x_{\rm work})=(y_{\rm index},y_{\rm clock},y_{\rm flag},y_{\rm work}).
--   $$
--
--   This is the register-partition identity needed to place the original verifier calls inside SELECT.
-- source:
--   Local source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BlockVerifierCoordinates.lean:11-64; paper: QMA has perfect completeness, Sabee Grewal and Dorian Rudolph, user-provided main.tex.

/- Generated from Solutions.BlockVerifierCoordinates by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition



/-! The two literal verifier calls in logical block coordinates, with arbitrary workspace. -/
open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.BlockVerifierCoordinates
end QMAPerfectCompleteness.Main.BlockVerifierCoordinates
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.BlockVerifierCoordinates
open BlockCircuit BlockCoordinates ReversibleGadgets

set_option maxHeartbeats 2000000

theorem QMAPerfectCompleteness.Main.BlockVerifierCoordinates.spectator_mask (V : Verifier gatesG2) (w : ℕ)
    (y x : Basis (bodyWires V+w)) :
    (∀ j, (∀ a, verifierEmbedding (V := V) w a ≠ j) → y j = x j) ↔
      (y ∘ indexWire = x ∘ indexWire) ∧ (y ∘ clockWire = x ∘ clockWire) ∧
        y flagWire = x flagWire ∧ (y ∘ workspaceWire = x ∘ workspaceWire) := by sorry
