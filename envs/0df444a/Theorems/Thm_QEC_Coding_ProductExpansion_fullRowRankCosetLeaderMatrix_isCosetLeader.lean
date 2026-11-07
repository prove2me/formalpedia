-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_fullRowRankCosetLeaderMatrix_isCosetLeader
-- name    : QEC.Coding.ProductExpansion.fullRowRankCosetLeaderMatrix_isCosetLeader
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:03:55.928679+00:00
-- url     : https://prove2.me/theorems/4a27b072-d685-48bf-9312-7b828dabdc2a
-- title:
--   Product Expansion: full Row Rank Coset Leader Matrix is Coset Leader
-- statement:
--   Every row selected by the maximal-row-rank constructor is a syndrome
--   coset leader.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L132-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L132-L138

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq W]

theorem QEC.Coding.ProductExpansion.fullRowRankCosetLeaderMatrix_isCosetLeader
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (z : Matrix W R F) (i : W) :
    IsCosetLeader h (z i) (row (fullRowRankCosetLeaderMatrix h hRank z) i) := by sorry
