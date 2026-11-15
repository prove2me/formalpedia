-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_ThresholdPreparation_Layout_copies_odd_word
-- name    : QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.copies_odd_word
-- status  : Proved
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:46:07.946195+00:00
-- url     : https://prove2.me/theorems/9f63afe3-f3b2-4c34-908c-c31c7d113073
-- title:
--   Shifted certificate words after the copy circuit
-- statement:
--   If the threshold-word registers initially contain zero, either odd-numbered word among the first four copy destinations contains the corresponding certificate source shifted left by one bit, with zero extension. Bits are ordered little-endian.
--
--   $$
--   \operatorname{word}_d(\operatorname{copy}(x))=0::\bigl(\operatorname{source}_d(x)\mathbin{++}[0]\bigr)\qquad(d\in\{1,3\}).
--   $$
--
--   In little-endian order, the leading zero doubles the source value. These two banks supply the words for twice each certificate integer.
-- source:
--   Local source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/ThresholdPreparation.lean:163-190; paper: QMA has perfect completeness, Sabee Grewal and Dorian Rudolph, user-provided main.tex.

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

theorem QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.copies_odd_word (x : Basis n) (hz : ∀ d j, x (L.wire (.word d j)) = false)
    (d : Fin 4) (hd : d.val%2=1) :
    (fun j => L.copyState x (L.wire (.word ⟨d.val,(
                                                    have this : @LT.lt.{0} Nat instLTNat (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) d) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) :=
                                                      @Fin.isLt (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) d;
                                                    @Decidable.byContradiction (@LT.lt.{0} Nat instLTNat (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) d) (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                                                      (Nat.decLt (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) d) (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                                                      fun (a : Not (@LT.lt.{0} Nat instLTNat (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) d) (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))) =>
                                                      QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.target_odd._proof_1 d hd a
                                                  )⟩ j))) =
      Fin.cons false (Fin.append (fun j => x (L.source (d,j))) (fun _ : Fin 1 => false)) := by sorry
