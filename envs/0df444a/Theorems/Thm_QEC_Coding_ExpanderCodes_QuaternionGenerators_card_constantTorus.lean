-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_card_constantTorus
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.card_constantTorus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:32:46.040563+00:00
-- url     : https://prove2.me/theorems/5f8c51e0-3a5f-42b9-a953-b94594b537ce
-- title:
--   Quaternion Generators: card constant Torus
-- statement:
--   The constant nonsplit torus has exactly `q + 1` elements even when the
--   coefficient field is much larger than the constant field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorus.lean#L116-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorus.lean#L116-L148

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.Coset.Card
import Lean.Elab.Tactic.Omega
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.card_constantTorus (f : F →+* K) (epsilon : F) (y : K)
    [Fintype F] (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Nat.card (constantTorus f epsilon y) = Fintype.card F + 1 := by sorry
