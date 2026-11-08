-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSGeneratorMatrixListMachine_sourceDirection_decode
-- name    : QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine.sourceDirection_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:34:15.48604+00:00
-- url     : https://prove2.me/theorems/c6231825-8f3e-4652-a691-b090e6112433
-- title:
--   LPSGenerator Matrix List Machine: source Direction decode
-- statement:
--   Actual finite instruction construction or proved invariant, whole execution, budget or source certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGeneratorMatrixListMachine.lean#L222-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGeneratorMatrixListMachine.lean#L222-L228

import Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixListQuery
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionMatrixMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open QEC.Coding.TannerLiftedProduct Turing StateTransition FieldProjection MatrixListQuery
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine.sourceDirection_decode {p:ℕ} (hp:p.Prime) (hp4:p%4=1) (n:ℕ) (j:Fin (p+1)) :
    (QuotientGroup.mk (generatorSL (lpsEffectiveResiduePrimeAt hp hp4 n)
      (lpsFinGeneratorEquiv (card_lpsQuaternionShell_eq_prime_add_one hp hp4) j)):
      PSL(2,ZMod (lpsEffectiveResiduePrimeAt hp hp4 n).q))=
        lpsFinQuaternionFamilyLabel hp hp4 (card_lpsQuaternionShell_eq_prime_add_one hp hp4) n j := by sorry
