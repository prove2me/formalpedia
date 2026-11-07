-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_fullRowRankCosetLeaderMatrix_productKernel
-- name    : QEC.Coding.ProductExpansion.fullRowRankCosetLeaderMatrix_productKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:03:57.452882+00:00
-- url     : https://prove2.me/theorems/3155fe3f-4df1-45c6-9ffc-3a44590b8eea
-- title:
--   Product Expansion: full Row Rank Coset Leader Matrix product Kernel
-- statement:
--   If the prescribed syndrome is killed by the second check, the
--   maximal-row-rank coset-leader matrix is a product-kernel word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L153-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L153-L160

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq W] [Fintype R']

theorem QEC.Coding.ProductExpansion.fullRowRankCosetLeaderMatrix_productKernel
    (h : Matrix R W F) (h' : Matrix R' W F)
    (hRank : h.rank = Fintype.card R) (z : Matrix W R F)
    (hz : h' * z = 0) :
    ProductKernel h h' (fullRowRankCosetLeaderMatrix h hRank z) := by sorry
