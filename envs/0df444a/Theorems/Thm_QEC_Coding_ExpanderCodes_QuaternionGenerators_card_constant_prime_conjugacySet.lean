-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_card_constant_prime_conjugacySet
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.card_constant_prime_conjugacySet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:35:13.69089+00:00
-- url     : https://prove2.me/theorems/31333572-8e81-445d-a2cb-a22ede72c40a
-- title:
--   Quaternion Generators: card constant prime conjugacy Set
-- statement:
--   The second constant-torus orbit also has exactly `q + 1` elements.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L199-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticGeneratorSets.lean#L199-L209

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.card_constant_prime_conjugacySet (f : F →+* K) (epsilon : F) (y : K)
    [Fintype F] (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) :
    Nat.card (conjugacySet (constantTorus f epsilon y)
      (projectivePrime (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne)) =
        Fintype.card F + 1 := by sorry
