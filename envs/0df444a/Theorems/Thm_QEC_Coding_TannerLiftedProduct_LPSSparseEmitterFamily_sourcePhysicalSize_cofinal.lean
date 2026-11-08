-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSSparseEmitterFamily_sourcePhysicalSize_cofinal
-- name    : QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily.sourcePhysicalSize_cofinal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:48:02.132226+00:00
-- url     : https://prove2.me/theorems/fa2dcc5f-2726-4e29-864a-40dccc3c0f18
-- title:
--   LPSSparse Emitter Family: source Physical Size cofinal
-- statement:
--   The LPSSparse Emitter Family construction uses the source Physical Size cofinal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterFamilyMachine.lean#L110-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterFamilyMachine.lean#L110-L114

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterSourceMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPrimeMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterFamilyMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily.sourcePhysicalSize_cofinal {p r r':ℕ} (hp:p.Prime) (hp4:p%4=1):
 ∀ N:ℕ,∃ B,N ≤ physicalSize (lpsEffectiveResiduePrimeAt hp hp4 B) (p+1) r r':= by sorry
