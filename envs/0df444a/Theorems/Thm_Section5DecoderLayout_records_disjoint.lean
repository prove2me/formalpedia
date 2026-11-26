-- Prove2me | Theorems.Thm_Section5DecoderLayout_records_disjoint
-- name    : Section5DecoderLayout.records_disjoint
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:56:52.385453+00:00
-- url     : https://prove2.me/theorems/9de1e236-05da-520b-8cbd-932d99962dc5
-- title:
--   Disjointness of canonical decoder column records
-- statement:
--   For any natural layout parameters N,K,b,f, let records_j embed the score and complex column payload of column j into the canonical decoder wires. Distinct column records are disjoint: $$i\ne j\implies\forall e,g:\ \operatorname{records}_i(e)\ne\operatorname{records}_j(g).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5DecoderLayoutLaws.lean, lines 60–61.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5DecoderLayout
import Definitions.Def_Section5Verified_Section5DecoderLayoutLaws
import Mathlib
import Theorems.Thm_Section5DecoderLayout_records_columnLabel
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout

theorem Section5DecoderLayout.records_disjoint {N K b f : ℕ} (i j : Fin (N+1)) (hij : i ≠ j) :
    ∀ e g, Section5DecoderLayout.records (K:=K) (b:=b) (f:=f) i e ≠ Section5DecoderLayout.records j g := by sorry
