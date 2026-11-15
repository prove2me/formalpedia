-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_ThresholdPreparation_Layout_values
-- name    : QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.values
-- status  : Proved
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:46:51.694253+00:00
-- url     : https://prove2.me/theorems/17a58728-a8d2-4454-a017-57b988c2acac
-- title:
--   Exact values of the six dynamic certificate thresholds
-- statement:
--   On clean arithmetic workspace, the six prepared threshold words have values a, 2a, b, 2b, 3a, and 3a+b, where a and b are the two k-bit certificate values.
--
--   $$
--   (w_0,w_1,w_2,w_3,w_4,w_5)=(a,2a,b,2b,3a,3a+b).
--   $$
--
--   Here each word is interpreted as a little-endian natural number. These are exactly the dynamic thresholds used for validity tests and SELECT.
-- source:
--   Local source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/ThresholdPreparation.lean:350-378; paper: QMA has perfect completeness, Sabee Grewal and Dorian Rudolph, user-provided main.tex.

/- Generated from Solutions.ThresholdPreparation by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition



/-! Certificate-dependent binary threshold preparation. Arithmetic registers are explicit
physical wires; their values may be retained as certificate-dependent ancillary garbage. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.ThresholdPreparation
end QMAPerfectCompleteness.Main.ThresholdPreparation
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.ThresholdPreparation
open BooleanCircuits ComparisonCircuits





namespace QMAPerfectCompleteness.Main.ThresholdPreparation.Layout
end QMAPerfectCompleteness.Main.ThresholdPreparation.Layout
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.ThresholdPreparation QMAPerfectCompleteness.Main.ThresholdPreparation.Layout
variable {k n : ℕ} (L : Layout k n)

theorem QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.values (x : Basis n) (hx : L.Clean x) :
    ∀ d : Fin 6, littleValue (fun j => L.state x (L.wire (.word d j))) =
      (![L.value x 0,2*L.value x 0,L.value x 1,2*L.value x 1,
        3*L.value x 0,3*L.value x 0+L.value x 1] : Fin 6 → ℕ) d := by sorry
