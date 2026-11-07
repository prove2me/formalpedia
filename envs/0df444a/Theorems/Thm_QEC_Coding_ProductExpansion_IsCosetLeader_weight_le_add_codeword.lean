-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_IsCosetLeader_weight_le_add_codeword
-- name    : QEC.Coding.ProductExpansion.IsCosetLeader.weight_le_add_codeword
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:03:28.942816+00:00
-- url     : https://prove2.me/theorems/c98c4bb1-d601-4382-9701-9bed49b93fe5
-- title:
--   Is Coset Leader: weight le add codeword
-- statement:
--   Adding a local-code word cannot lighten a syndrome coset leader.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L70-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L70-L79

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.IsCosetLeader.weight_le_add_codeword
    {h : Matrix R W F} {y : R → F} {x : Word F W}
    (hx : IsCosetLeader h y x)
    (c : Word F W) (hc : c ∈ (parityCheckCode h).carrier) :
    HammingWeight x ≤ HammingWeight (x + c) := by sorry
