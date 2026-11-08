-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_carrier_iff_lpsEncodedOutput
-- name    : QEC.Coding.TannerLiftedProduct.mem_carrier_iff_lpsEncodedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:16:00.822758+00:00
-- url     : https://prove2.me/theorems/60a4c8cf-4230-4b15-bef8-ffe05e9aa066
-- title:
--   Tanner Lifted Product: mem carrier iff lps Encoded Output
-- statement:
--   All computed scalar checks cut out exactly the actual Tanner CSS carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L400-L418
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L400-L418

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_93e0e40f7b_113
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_93e0e40f7b_307
open FiniteFieldPauli

theorem QEC.Coding.TannerLiftedProduct.mem_carrier_iff_lpsEncodedOutput {q D r r' s : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F] (e : Fin s ≃ F)
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F)
    (ψ : Semantics.Qudit.QuditRegister (fun _ : LiftedProduct.QubitIndex
      (Fin 2 × Fin r) (Fin D) (Fin D) (Fin 2 × Fin r') PSL(2, ZMod q) => Fintype.card F)) :
    ψ ∈ (semanticPresentation (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h').code.carrier ↔
      ∀ i, lpsEncodedOutputOperator e (encodedFieldTables e) label
        (h.map e.symm) (h'.map e.symm) i ψ = ψ := by sorry
