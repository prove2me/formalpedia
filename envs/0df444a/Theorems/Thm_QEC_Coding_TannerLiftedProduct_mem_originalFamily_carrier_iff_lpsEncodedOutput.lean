-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_originalFamily_carrier_iff_lpsEncodedOutput
-- name    : QEC.Coding.TannerLiftedProduct.mem_originalFamily_carrier_iff_lpsEncodedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:16:22.385201+00:00
-- url     : https://prove2.me/theorems/84bb6b5d-211b-4b0f-b714-a36640754064
-- title:
--   Tanner Lifted Product: mem original Family carrier iff lps Encoded Output
-- statement:
--   The original PK22 family is cut out by these complete numeric scalar checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L422-L443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L422-L443

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_93e0e40f7b_113
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_93e0e40f7b_307
open FiniteFieldPauli

theorem QEC.Coding.TannerLiftedProduct.mem_originalFamily_carrier_iff_lpsEncodedOutput {p D r r' s : ℕ}
    {F : Type} [Field F] [Fintype F] (e : Fin s ≃ F)
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ)
    (generators : Fin D → LPSGeneratorIndex p)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (ψ : Semantics.Qudit.QuditRegister (fun _ : LiftedProduct.QubitIndex
      (Fin 2 × Fin r) (Fin D) (Fin D) (Fin 2 × Fin r')
      PSL(2, ZMod (lpsResiduePrimeSequence hp hp4 n).q) => Fintype.card F)) :
    ψ ∈ (semanticPresentation (fun j => lpsQuaternionFamilyLabel hp hp4 n (generators j))
      h h').code.carrier ↔
      ∀ i, lpsEncodedOutputOperator e (encodedFieldTables e)
        (fun j => lpsEffectiveQuaternionFamilyIndex hp hp4 n (generators j))
        (h.map e.symm) (h'.map e.symm) i ψ = ψ := by sorry
