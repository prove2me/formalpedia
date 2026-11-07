-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_cosetLeaderMatrix_productKernel
-- name    : QEC.Coding.ProductExpansion.cosetLeaderMatrix_productKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:03:46.749116+00:00
-- url     : https://prove2.me/theorems/044fb6fd-3b9e-496d-a800-32c969990531
-- title:
--   Product Expansion: coset Leader Matrix product Kernel
-- statement:
--   If the prescribed syndrome is killed by the second local check, the
--   row-leader matrix is an actual product-kernel word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L120-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L120-L127

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq W] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.cosetLeaderMatrix_productKernel
    (h : Matrix R W F) (h' : Matrix R' W F)
    (z : Matrix W R F) (x₀ : Matrix W W F)
    (hx₀ : ∀ i, h.mulVec (row x₀ i) = z i)
    (hz : h' * z = 0) :
    ProductKernel h h' (cosetLeaderMatrix h z x₀ hx₀) := by sorry
