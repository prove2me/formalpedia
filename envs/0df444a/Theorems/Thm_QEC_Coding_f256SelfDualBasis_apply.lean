-- Prove2me | Theorems.Thm_QEC_Coding_f256SelfDualBasis_apply
-- name    : QEC.Coding.f256SelfDualBasis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:23:55.537194+00:00
-- url     : https://prove2.me/theorems/58051f4a-ea15-47eb-9d92-07be96982027
-- title:
--   Coding: f256 Self Dual Basis apply
-- statement:
--   The Coding construction uses the f256 Self Dual Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/SelfDualBasis.lean#L374-L385
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/SelfDualBasis.lean#L374-L385

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Field
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
set_option autoImplicit false
open Polynomial
open scoped Matrix
open QEC QEC.Coding

theorem QEC.Coding.f256SelfDualBasis_apply (i : Fin 8) :
    f256SelfDualBasis i =
      (f256PolynomialBasis ᵥ* f256SelfDualP.map (algebraMap (ZMod 2) F256)) i := by sorry
