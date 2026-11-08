-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResidueY_eq_minusRoot
-- name    : QEC.Coding.TannerLiftedProduct.lpsResidueY_eq_minusRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:18:47.340567+00:00
-- url     : https://prove2.me/theorems/55121a01-7b9a-4218-9e5e-77ce23e30787
-- title:
--   Tanner Lifted Product: lps Residue Y eq minus Root
-- statement:
--   The original source residue-pair second coordinate is the same least numerical root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSquareRootMachine.lean#L211-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSquareRootMachine.lean#L211-L214

import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRoot
import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRootInput
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSquareRootMachine
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsResidueY_eq_minusRoot (a : LPSResiduePrime p) :
    lpsResidueY a.q=(SquareRoot.index (a.q-1) a.q (lpsMinusRoot_numeric_exists a):ZMod a.q) := by sorry
