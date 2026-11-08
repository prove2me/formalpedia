-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_encodedSparseRegion
-- name    : QEC.Coding.TannerLiftedProduct.mem_encodedSparseRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:14:55.066181+00:00
-- url     : https://prove2.me/theorems/ea7371bb-9b0d-4e72-b157-184ca643cff8
-- title:
--   Tanner Lifted Product: mem encoded Sparse Region
-- statement:
--   The Tanner Lifted Product construction uses the mem encoded Sparse Region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L91-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L91-L99

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.mem_encodedSparseRegion {F : Type} [Field F] {n s : ℕ}
    (e : Fin s ≃ F) (row : List (Fin n × Fin s)) (x : Fin n) :
    x ∈ encodedSparseRegion (encodedFieldTables e) row ↔
      lpsSparseRowValue (row.map fun entry => (entry.1, e entry.2)) x ≠ 0 := by sorry
