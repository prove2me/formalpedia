-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_BlockProof_cyclicOp_decomposition
-- name    : QMAPerfectCompleteness.Main.BlockProof.cyclicOp_decomposition
-- status  : Proved
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:44:11.231571+00:00
-- url     : https://prove2.me/theorems/abb42b26-519c-4738-b6cf-0b6560b301f4
-- title:
--   Decomposition of the cyclic constraint into two gadget blocks
-- statement:
--   For a verifier V, a computational basis proof z, and a real parameter Γ, the cyclic operator satisfies C(z,Γ)=2F+Γ⁻¹W(z), where F is the forward gadget block and W(z) is the closing gadget block. The identity also holds at Γ=0 with Lean’s total inverse convention.
--
--   $$
--   C_{z,\Gamma}=2F+\Gamma^{-1}W_z.
--   $$
--
--   The identity separates the two logical gadget blocks used to construct the cyclic block encoding.
-- source:
--   Local source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BlockEncoding.lean:272-296; paper: QMA has perfect completeness, Sabee Grewal and Dorian Rudolph, user-provided main.tex.

/- Generated from Solutions.BlockEncoding by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates



/-! Algebraic ingredients of Lemma 3.6. All results in this file are proved from definitions;
no import of the open `exact_block_encoding` statement is used. -/

open Matrix
open scoped Kronecker

namespace QMAPerfectCompleteness.Main.BlockProof
end QMAPerfectCompleteness.Main.BlockProof
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.BlockProof

variable {G : GateSet} (V : Verifier G)

theorem QMAPerfectCompleteness.Main.BlockProof.cyclicOp_decomposition (z : V.Proof) (Γ : ℝ) :
    V.cyclicOp z Γ = (2 : ℂ) • forwardBlock V + ((Γ⁻¹ : ℝ) : ℂ) • closingBlock V z := by sorry
