-- Prove2me | Theorems.Thm_QMAPerfectCompleteness_Main_BlockProof_exact_block_identity
-- name    : QMAPerfectCompleteness.Main.BlockProof.exact_block_identity
-- status  : Proved
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:44:46.147833+00:00
-- url     : https://prove2.me/theorems/14b42728-e428-4943-9ce7-ad7de006d6bc
-- title:
--   Exact selected block of the certificate unitary
-- statement:
--   Let V be a G₂ verifier and let (a,b) be a valid certificate. With k the index-register width, the block selected between flag 1 and flag 0 in the unitary U(z,a,b) is (a/2ᵏ)(I−C(z,a/b)). This is the algebraic identity in Lemma 3.6.
--
--   $$
--   \operatorname{block}_{0,1}U_{z,a,b}=\frac{a}{2^k}\bigl(I-C_{z,a/b}\bigr).
--   $$
--
--   The index and verifier-ancilla registers are selected at zero, with incoming flag one and outgoing flag zero. This identifies the consistency residual with the physical rejection amplitude.
-- source:
--   Local source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BlockEncoding.lean:298-325; paper: QMA has perfect completeness, Sabee Grewal and Dorian Rudolph, user-provided main.tex.

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

theorem QMAPerfectCompleteness.Main.BlockProof.exact_block_identity (V : Verifier gatesG2) (z : V.Proof) (a b : ℕ)
    (hvalid : IsValidCertificate V a b) :
    (V.zEmbed (indexQubits V) false)ᴴ * V.blockUnitary (indexQubits V) z a b *
        V.zEmbed (indexQubits V) true =
      ((a : ℂ) / (2 : ℂ) ^ indexQubits V) • (1 - V.cyclicOp z ((a : ℝ) / b)) := by sorry
