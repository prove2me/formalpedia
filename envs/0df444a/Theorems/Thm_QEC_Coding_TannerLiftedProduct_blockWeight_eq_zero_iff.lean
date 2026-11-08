-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_blockWeight_eq_zero_iff
-- name    : QEC.Coding.TannerLiftedProduct.blockWeight_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:36:17.802432+00:00
-- url     : https://prove2.me/theorems/b8f8b03b-b66c-4a90-9908-57da92ce9331
-- title:
--   Tanner Lifted Product: block Weight eq zero iff
-- statement:
--   Zero block weight detects exactly the zero middle chain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1029-L1060
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1029-L1060

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

theorem QEC.Coding.TannerLiftedProduct.blockWeight_eq_zero_iff
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    blockWeight c = 0 ↔ c = 0 := by sorry
