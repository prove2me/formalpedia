-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_cosetLeaderMatrix_isCosetLeader
-- name    : QEC.Coding.ProductExpansion.cosetLeaderMatrix_isCosetLeader
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:23.993953+00:00
-- url     : https://prove2.me/theorems/5b6ea7fd-0b95-4683-aca9-39a20a368939
-- title:
--   Product Expansion: coset Leader Matrix is Coset Leader
-- statement:
--   Every selected row is the promised syndrome coset leader.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L98-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L98-L103

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq W] [Fintype R]

theorem QEC.Coding.ProductExpansion.cosetLeaderMatrix_isCosetLeader
    (h : Matrix R W F) (z : Matrix W R F) (x₀ : Matrix W W F)
    (hx₀ : ∀ i, h.mulVec (row x₀ i) = z i) (i : W) :
    IsCosetLeader h (z i) (row (cosetLeaderMatrix h z x₀ hx₀) i) := by sorry
