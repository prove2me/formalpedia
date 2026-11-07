-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_parityCheckCode_generatorImageParityCheck_carrier
-- name    : QEC.Coding.ProductExpansion.parityCheckCode_generatorImageParityCheck_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:35:54.395264+00:00
-- url     : https://prove2.me/theorems/a9f898cb-8514-44af-acbd-9e22cbaee863
-- title:
--   Product Expansion: parity Check Code generator Image Parity Check carrier
-- statement:
--   The parity-check-code carrier of the constructed matrix is the image of
--   the original generator matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L865-L870
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L865-L870

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [DecidableEq F] [Fintype R']

theorem QEC.Coding.ProductExpansion.parityCheckCode_generatorImageParityCheck_carrier
    (g : Matrix R W F) :
    (parityCheckCode (generatorImageParityCheck g)).carrier = generatorImage g := by sorry
