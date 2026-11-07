-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_card_constant_conjugacySet
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.card_constant_conjugacySet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:34:50.353619+00:00
-- url     : https://prove2.me/theorems/f586ff0a-5eca-43b9-9891-75e08beef40d
-- title:
--   Quaternion Generators: card constant conjugacy Set
-- statement:
--   The constant-torus first generator orbit has the asserted `q + 1` elements.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L131-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L131-L140

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.card_constant_conjugacySet (f : F →+* K) (epsilon : F) (y : K)
    [Fintype F] (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) :
    Nat.card (conjugacySet (constantTorus f epsilon y)
      (projectiveBase (f epsilon) y hY hOne)) = Fintype.card F + 1 := by sorry
