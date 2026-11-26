-- Prove2me | Theorems.Thm_Section5DecoderLayout_records_columnLabel
-- name    : Section5DecoderLayout.records_columnLabel
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:53:47.47254+00:00
-- url     : https://prove2.me/theorems/7b871711-197a-4642-bc26-2c834e99d34e
-- title:
--   Every wire in a decoder record has its record's column label
-- statement:
--   Let $N,K,b,f$ be natural numbers. The decoder layout assigns a record to each column $j\in\{0,\ldots,N\}$, consisting of its score register and the real and imaginary payload registers of column $j$ of the matrix at stage $K$. Its record width is $R=2(N+1)+2b+1+2(N+1)(b+1)$. Let $r_j(e)$ be the physical wire at position $e<R$ of this record and let $c$ be the bijection encoding logical wires as physical wire indices. The column-label function assigns a matrix wire its matrix column, a score wire its score column, and no label to other wire types. Then
--
--   $$
--   \operatorname{columnLabel}(c^{-1}(r_j(e)))=\operatorname{some}(j)\qquad(j\le N,\ e<R).
--   $$
--
--   This identifies the column associated with every score or payload wire in a record and supports separation of different column records.
-- source:
--   Original auxiliary decoder-layout result supporting the Section 5 formalization of https://arxiv.org/html/2609.40331v3. Exact source: Solutions/Section5DecoderLayoutLaws.lean, Section5DecoderLayout.records_columnLabel, lines 32–58; columnLabel is defined at lines 27–30. Record construction and widths: Solutions/Section5DecoderLayout.lean, lines 11–13 and 112–120. This is a formalization-specific layout lemma, not a separately numbered theorem of the paper.

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
import Definitions.Def_Section5Verified_Section5ComplexMatrixCircuit
import Definitions.Def_Section5Verified_Section5DecoderLayout
import Definitions.Def_Section5Verified_Section5DecoderLayoutLaws
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout

theorem Section5DecoderLayout.records_columnLabel {N K b f : ℕ} (j : Fin (N+1)) (e : Fin (Section5DecoderLayout.recordWidth N b)) :
    Section5DecoderLayout.columnLabel ((Section5DecoderLayout.code N K b f).symm (Section5DecoderLayout.records j e))=some j := by sorry
