-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_fullRowRankCosetLeaderMatrix_mul_transpose
-- name    : QEC.Coding.ProductExpansion.fullRowRankCosetLeaderMatrix_mul_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:37:09.167275+00:00
-- url     : https://prove2.me/theorems/5d8bab17-8689-4390-9985-04ac5cc2771c
-- title:
--   Product Expansion: full Row Rank Coset Leader Matrix mul transpose
-- statement:
--   The maximal-row-rank constructor has exactly its prescribed syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L142-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L142-L148

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq W]

theorem QEC.Coding.ProductExpansion.fullRowRankCosetLeaderMatrix_mul_transpose
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (z : Matrix W R F) :
    fullRowRankCosetLeaderMatrix h hRank z * h.transpose = z := by sorry
