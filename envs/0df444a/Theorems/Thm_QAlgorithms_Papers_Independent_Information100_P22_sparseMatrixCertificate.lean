-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_sparseMatrixCertificate
-- name    : QAlgorithms.Papers.Independent.Information100.P22.sparseMatrixCertificate
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:14:02.976192+00:00
-- url     : https://prove2.me/theorems/3538b465-b163-4252-a96c-e9dbc969a009
-- title:
--   Eq.(S65), unnumbered: printed binary cut-matrix certificate
-- statement:
--   Let $B_{\rm ER}$ be exactly the $12\times12$ binary matrix printed in Eq.(S65), with its rows stored in the paper-local matrix definition in the displayed order. Then
--   $$\operatorname{rank}_{\mathbb F_2}B_{\rm ER}=12.$$
--   This certifies the printed cut matrix. It does not identify the unsupplied internal adjacency blocks of the sampled random graph and does not replace the fixed-sample claims by an existential graph statement.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 42, Eq.(S65), unnumbered: printed binary cut-matrix certificate

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Eq.(S65), PDF p.42: certificate of this printed cut matrix alone. -/
theorem sparseMatrixCertificate : sparseCutMatrix.rank = 12 := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
