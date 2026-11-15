-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_CircuitRecipe_Gadgets_eval_compareBits
-- name    : QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.eval_compareBits
-- status  : Proved
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:44:31.384879+00:00
-- url     : https://prove2.me/theorems/581aede7-835a-4f7c-9423-1dd5f37c25d6
-- title:
--   Exact evaluation of the bit-comparison circuit recipe
-- statement:
--   Fix an expression environment and loop context. If the evaluated control and flag expressions describe a raw AND layout of the evaluated width, and the bit expression describes a Boolean pattern p, then the comparison recipe evaluates to precisely the raw comparison gate list for that layout, pattern, and evaluated target.
--
--   $$
--   \operatorname{eval}(\operatorname{compareBits},\mathrm{env},\mathrm{ctx},\mathrm{src})=\operatorname{compareGates}(L,p,\operatorname{eval}(\mathrm{target})).
--   $$
--
--   The equality is for ordered raw instruction lists, providing an executable recipe interface to the comparison gadget.
-- source:
--   Local source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RecipeGadgets.lean:340-388; paper: QMA has perfect completeness, Sabee Grewal and Dorian Rudolph, user-provided main.tex.

/- Generated from Solutions.RecipeGadgets by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawArithmeticGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RawControlGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeNormalization
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



/-! Finite recipes realizing the linear reversible circuit templates. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QMAPerfectCompleteness.Main.CircuitRecipe
end QMAPerfectCompleteness.Main.CircuitRecipe
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CircuitRecipe

namespace QMAPerfectCompleteness.Main.CircuitRecipe.Expr
end QMAPerfectCompleteness.Main.CircuitRecipe.Expr
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CircuitRecipe QMAPerfectCompleteness.Main.CircuitRecipe.Expr


end

namespace QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets
end QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.CircuitRecipe QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets
open RawG2 RawEncoding

theorem QMAPerfectCompleteness.Main.CircuitRecipe.Gadgets.eval_compareBits (r control flags bits target : Expr) (env : Environment) (ctx : List ℕ) (src)
    (L : RawG2.AndLayout (r.eval env ctx)) (p : Fin (r.eval env ctx) → Bool)
    (hc : ∀j,L.controls j=control.eval env ctx j.val)
    (hf : ∀j,L.flags j=flags.eval env ctx j.val)
    (hb : ∀j,bits.eval env ctx j.val=if p j then 1 else 0) :
    (compareBits r control flags bits target).eval env ctx src=RawG2.compareGates L p (target.eval env ctx) := by sorry
