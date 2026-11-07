-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_lightGenerators_restrictedWeight_lt_one_sixth
-- name    : QEC.Coding.ProductExpansion.lightGenerators_restrictedWeight_lt_one_sixth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:33:06.004192+00:00
-- url     : https://prove2.me/theorems/14f50414-0639-43b3-afc4-245d9a916846
-- title:
--   Product Expansion: light Generators restricted Weight lt one sixth
-- statement:
--   The total restricted weight of the light generators is below `d/6`.
--   This threshold formulation replaces the paper's sorted-prefix choice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1142-L1176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1142-L1176

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype F] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.lightGenerators_restrictedWeight_lt_one_sixth
    (A : Finset W) (C : Finset (Word F W)) (d : Nat)
    (hCPositive : 0 < C.card) (hDPositive : 0 < d) :
    (generatorRestrictedWeight A (lightGenerators A C d) : ℝ) < (d : ℝ) / 6 := by sorry
