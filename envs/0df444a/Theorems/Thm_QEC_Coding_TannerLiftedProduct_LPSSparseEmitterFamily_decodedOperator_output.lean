-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterFamily_decodedOperator_output
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily.decodedOperator_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:42:29.668045+00:00
-- url     : https://prove2.me/theorems/041faecd-08a7-48ce-a98d-30d0fed6104c
-- title:
--   LPSSparse Emitter Family: decoded Operator output
-- statement:
--   The LPSSparse Emitter Family construction uses the decoded Operator output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterFamilyMachine.lean#L133-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterFamilyMachine.lean#L133-L147

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterSourceMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPrimeMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterFamilyMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open scoped MatrixGroups
open FiniteFieldPauli
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily._p2m_local_instance_6058dbc402_120

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily.decodedOperator_output {p D r r' s:ℕ} {F:Type} [Field F] [Fintype F]
 (e:Fin s≃F) (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p)
 (h:Matrix (Fin r) (Fin D) F) (h':Matrix (Fin r') (Fin D) F)
 (i:Fin (CheckCount (lpsEffectiveResiduePrimeAt hp hp4 B).q D r r' s)):
 decodedOperator e (encodedFieldTables e) i
 (output hp hp4 B g (encodedFieldTables e) (h.map e.symm) (h'.map e.symm))=
 lpsEncodedOutputOperator e (encodedFieldTables e) (fun j=>lpsEffectiveQuaternionFamilyIndex hp hp4 B (g j))
 (h.map e.symm) (h'.map e.symm) i:= by sorry
