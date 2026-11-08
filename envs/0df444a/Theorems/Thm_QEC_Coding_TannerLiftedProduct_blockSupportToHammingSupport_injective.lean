-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_blockSupportToHammingSupport_injective
-- name    : QEC.Coding.TannerLiftedProduct.blockSupportToHammingSupport_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:38:41.305572+00:00
-- url     : https://prove2.me/theorems/3ef2283a-6165-4c46-b534-2edf7b5a2e42
-- title:
--   Tanner Lifted Product: block Support To Hamming Support injective
-- statement:
--   Distinct source blocks choose distinct scalar coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L983-L1011
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L983-L1011

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

theorem QEC.Coding.TannerLiftedProduct.blockSupportToHammingSupport_injective
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Function.Injective (blockSupportToHammingSupport c) := by sorry
