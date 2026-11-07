-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_coefficientEmbedding_injective
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.coefficientEmbedding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:32:49.480613+00:00
-- url     : https://prove2.me/theorems/c3c0e6c1-37fd-4b95-ad4a-74015838cbfa
-- title:
--   Quaternion Generators: coefficient Embedding injective
-- statement:
--   The Quaternion Generators construction uses the coefficient Embedding injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorus.lean#L34-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuadraticTorus.lean#L34-L39

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

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.coefficientEmbedding_injective (f : F →+* K) (epsilon : F) (y : K) :
    Function.Injective (coefficientEmbedding f epsilon y) := by sorry
