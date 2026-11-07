-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_cosetLeaderMatrix_mul_transpose
-- name    : QEC.Coding.ProductExpansion.cosetLeaderMatrix_mul_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:07.871214+00:00
-- url     : https://prove2.me/theorems/7df1eeb3-ac84-427e-976a-ff92a2ef3798
-- title:
--   Product Expansion: coset Leader Matrix mul transpose
-- statement:
--   The chosen row-leader matrix has exactly the prescribed right syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L107-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L107-L115

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq W] [Fintype R]

theorem QEC.Coding.ProductExpansion.cosetLeaderMatrix_mul_transpose
    (h : Matrix R W F) (z : Matrix W R F) (x₀ : Matrix W W F)
    (hx₀ : ∀ i, h.mulVec (row x₀ i) = z i) :
    cosetLeaderMatrix h z x₀ hx₀ * h.transpose = z := by sorry
