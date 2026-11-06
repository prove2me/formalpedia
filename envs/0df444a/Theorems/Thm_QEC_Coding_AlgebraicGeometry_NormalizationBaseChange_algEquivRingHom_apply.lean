-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_NormalizationBaseChange_algEquivRingHom_apply
-- name    : QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.algEquivRingHom_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:12:43.393556+00:00
-- url     : https://prove2.me/theorems/05108a14-5675-45e7-84e7-e6e2fb0c8115
-- title:
--   Normalization Base Change: alg Equiv Ring Hom apply
-- statement:
--   The Normalization Base Change construction uses the alg Equiv Ring Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/NormalizationBaseChange.lean#L14-L14
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/NormalizationBaseChange.lean#L14-L14

import Mathlib.AlgebraicGeometry.Pullbacks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

theorem QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.algEquivRingHom_apply (e : A ≃ₐ[R] B) (x : A) : e.toRingHom x = e x := by sorry
