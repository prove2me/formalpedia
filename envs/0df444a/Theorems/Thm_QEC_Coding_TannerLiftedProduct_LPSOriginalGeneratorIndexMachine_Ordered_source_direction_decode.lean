-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalGeneratorIndexMachine_Ordered_source_direction_decode
-- name    : QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered.source_direction_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:52:06.361333+00:00
-- url     : https://prove2.me/theorems/35bae82f-4fa5-49d5-a801-a48a5e6e0416
-- title:
--   Ordered: source direction decode
-- statement:
--   Effective-family indices decode to the exact original source family labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorIndexMachine.lean#L447-L452
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorIndexMachine.lean#L447-L452

import Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedFieldComputation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered._p2m_local_instance_8252a2e3b6_393

theorem QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered.source_direction_decode {p:ℕ} (hp:p.Prime) (hp4:p%4=1) (n:ℕ) (j:Fin (p+1)):
 (lpsPSLEnumerationEquiv (lpsEffectiveResiduePrimeAt hp hp4 n).q)
 (result (lpsEffectiveResiduePrimeAt hp hp4 n) (lpsFinGeneratorEquiv (card_lpsQuaternionShell_eq_prime_add_one hp hp4) j))=
 lpsFinQuaternionFamilyLabel hp hp4 (card_lpsQuaternionShell_eq_prime_add_one hp hp4) n j:= by sorry
