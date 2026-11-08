-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterFamily_mem_originalFamily_carrier_iff_decodedOutput
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily.mem_originalFamily_carrier_iff_decodedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:42:28.939573+00:00
-- url     : https://prove2.me/theorems/59a161fa-6568-4ba1-a26f-0d3d9e1be385
-- title:
--   LPSSparse Emitter Family: mem original Family carrier iff decoded Output
-- statement:
--   The LPSSparse Emitter Family construction uses the mem original Family carrier iff decoded Output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterFamilyMachine.lean#L148-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterFamilyMachine.lean#L148-L162

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterSourceMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPrimeMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterFamilyMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open scoped MatrixGroups
open FiniteFieldPauli
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily._p2m_local_instance_6058dbc402_120

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily.mem_originalFamily_carrier_iff_decodedOutput {p D r r' s:ℕ} {F:Type} [Field F] [Fintype F]
 (e:Fin s≃F) (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p)
 (h:Matrix (Fin r) (Fin D) F) (h':Matrix (Fin r') (Fin D) F)
 (ψ:Semantics.Qudit.QuditRegister (fun _:LiftedProduct.QubitIndex
   (Fin 2×Fin r) (Fin D) (Fin D) (Fin 2×Fin r') PSL(2,ZMod (lpsResiduePrimeSequence hp hp4 B).q)=>Fintype.card F)):
 ψ∈(semanticPresentation (fun j=>lpsQuaternionFamilyLabel hp hp4 B (g j)) h h').code.carrier↔
 ∀ i,decodedOperator e (encodedFieldTables e) i
 (output hp hp4 B g (encodedFieldTables e) (h.map e.symm) (h'.map e.symm)) ψ=ψ:= by sorry
