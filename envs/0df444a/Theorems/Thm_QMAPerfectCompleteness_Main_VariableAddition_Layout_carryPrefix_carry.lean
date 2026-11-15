-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_VariableAddition_Layout_carryPrefix_carry
-- name    : QMAPerfectCompleteness.Main.VariableAddition.Layout.carryPrefix_carry
-- status  : Proved
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:45:45.373389+00:00
-- url     : https://prove2.me/theorems/8634c692-8331-45be-83cb-a2516b44b0fd
-- title:
--   Correctness of the reversible adder carry prefix
-- statement:
--   For an r-bit adder layout with initially zero carry and temporary wires, after t≤r carry steps every carry position j≤t equals the binary-addition carry of the two original input words. This includes the overflow position j=r.
--
--   $$
--   (\operatorname{carryPrefix}_t(x))_{\operatorname{carry}(j)}=\operatorname{carry}_j(A,B,0),\qquad j\le t\le r.
--   $$
--
--   The words A and B are the original adder inputs. Including the final carry position supports the subsequent borrow and comparison constructions.
-- source:
--   Local source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/VariableAddition.lean:186-212; paper: QMA has perfect completeness, Sabee Grewal and Dorian Rudolph, user-provided main.tex.

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

theorem QMAPerfectCompleteness.Main.VariableAddition.Layout.carryPrefix_carry (t : ℕ) (ht : t ≤ r) (x : Basis n)
    (hcarry : ∀ j, x (L.carry j) = false) (hp : x L.temp = false)
    (j : Fin (r+1)) (hj : j.val ≤ t) :
    eval (L.carryPrefix t ht) x (L.carry j) =
      BitVec.carry j.val (L.leftWord x) (L.rightWord x) false := by sorry
