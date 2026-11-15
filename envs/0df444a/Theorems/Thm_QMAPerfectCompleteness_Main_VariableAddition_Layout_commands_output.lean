-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_VariableAddition_Layout_commands_output
-- name    : QMAPerfectCompleteness.Main.VariableAddition.Layout.commands_output
-- status  : Proved
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:46:19.729592+00:00
-- url     : https://prove2.me/theorems/fa43c7ad-3078-4769-9cff-609c20acf38f
-- title:
--   Output correctness of the reversible variable adder
-- statement:
--   With clean carry and temporary wires, the complete r-bit reversible adder XORs each original output bit with the corresponding bit of the sum of its two input words. The output register itself may initially contain arbitrary bits.
--
--   $$
--   (\operatorname{commands}(x))_{\operatorname{output}(j)}=x_{\operatorname{output}(j)}\mathbin{\oplus}\operatorname{bit}_j(A+B).
--   $$
--
--   The sum is r-bit addition of the original input words. This reversible output rule underlies certificate-dependent arithmetic without enumerating certificates.
-- source:
--   Local source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/VariableAddition.lean:348-372; paper: QMA has perfect completeness, Sabee Grewal and Dorian Rudolph, user-provided main.tex.

/- Generated from Solutions.VariableAddition by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition



/-! Literal variable-register addition using a ripple carry, copied sums, and uncomputation. -/
open Matrix
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace QMAPerfectCompleteness.Main.VariableAddition
end QMAPerfectCompleteness.Main.VariableAddition
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.VariableAddition
open BooleanCircuits ComparisonCircuits ClockCircuits















namespace QMAPerfectCompleteness.Main.VariableAddition.Layout
end QMAPerfectCompleteness.Main.VariableAddition.Layout
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.VariableAddition QMAPerfectCompleteness.Main.VariableAddition.Layout
variable {r n : ℕ} (L : Layout r n)

theorem QMAPerfectCompleteness.Main.VariableAddition.Layout.commands_output (x : Basis n) (hcarry : ∀ j, x (L.carry j) = false)
    (hp : x L.temp = false) (j : Fin r) :
    eval L.commands x (L.output j) =
      xor (x (L.output j)) ((L.leftWord x + L.rightWord x).getLsbD j) := by sorry
