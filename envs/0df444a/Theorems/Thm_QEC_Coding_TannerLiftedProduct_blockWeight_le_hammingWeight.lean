-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_blockWeight_le_hammingWeight
-- name    : QEC.Coding.TannerLiftedProduct.blockWeight_le_hammingWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:33:59.94546+00:00
-- url     : https://prove2.me/theorems/9ebf8c05-a994-4516-bf06-e1501faa3ca3
-- title:
--   Tanner Lifted Product: block Weight le hamming Weight
-- statement:
--   The source block weight never exceeds scalar Hamming weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1016-L1024
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1016-L1024

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [Group G] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.blockWeight_le_hammingWeight
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    blockWeight c ≤ HammingWeight c := by sorry
