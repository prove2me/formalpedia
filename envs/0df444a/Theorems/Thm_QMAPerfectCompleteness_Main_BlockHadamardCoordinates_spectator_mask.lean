-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_BlockHadamardCoordinates_spectator_mask
-- name    : QMAPerfectCompleteness.Main.BlockHadamardCoordinates.spectator_mask
-- status  : Proved
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:44:20.949978+00:00
-- url     : https://prove2.me/theorems/79012578-a9a3-478e-bb50-165ca327dfdf
-- title:
--   Complement of the index register in the block layout
-- statement:
--   For any G₂ verifier V, any workspace size w, and basis strings x and y on the block register, agreement outside the index wires is equivalent to agreement on the clock, verifier, flag, and workspace coordinates. No initialized-workspace assumption is needed.
--
--   $$
--   x=y\text{ outside the index bank}\iff(x_{\rm clock},x_{\rm verifier},x_{\rm flag},x_{\rm work})=(y_{\rm clock},y_{\rm verifier},y_{\rm flag},y_{\rm work}).
--   $$
--
--   This partition identity supplies the spectator conditions for the physical index-Hadamard bank.
-- source:
--   Local source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BlockHadamardCoordinates.lean:12-67; paper: QMA has perfect completeness, Sabee Grewal and Dorian Rudolph, user-provided main.tex.

/- Generated from Solutions.BlockHadamardCoordinates by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets



/-! The physical paired-H bank implements the logical H bank with clean workspace. -/
open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.BlockHadamardCoordinates
open BlockCircuit BlockCoordinates BlockCompiler

set_option maxHeartbeats 2000000

theorem QMAPerfectCompleteness.Main.BlockHadamardCoordinates.spectator_mask (V : Verifier gatesG2) (w : ℕ)
    (y x : Basis (bodyWires V+w)) :
    (∀ j, (∀ a, (indexWire (V := V) (w := w) a) ≠ j) → y j = x j) ↔
      (y ∘ clockWire = x ∘ clockWire) ∧ (y ∘ verifierWire = x ∘ verifierWire) ∧
        y flagWire = x flagWire ∧ (y ∘ workspaceWire = x ∘ workspaceWire) := by sorry
