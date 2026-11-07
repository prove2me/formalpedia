-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialToProjective_eq_one_of_fixed_projective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialToProjective_eq_one_of_fixed_projective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:43:53.319814+00:00
-- url     : https://prove2.me/theorems/aa67eafe-0eff-44c8-ba91-94fc3106ab48
-- title:
--   Cartwright Steger: special To Projective eq one of fixed projective
-- statement:
--   The Cartwright Steger construction uses the special To Projective eq one of fixed projective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/SpecialLinear.lean#L486-L517
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/SpecialLinear.lean#L486-L517

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Independence
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Matrix
open scoped commutatorElement
open scoped Pointwise
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialToProjective_eq_one_of_fixed_projective
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level))
    (hfix : ∀ x : ℙ (ResidueField P r level)
      (Fin r.matrixRank → ResidueField P r level), s • x = x) :
    specialToProjective P r level s = 1 := by sorry
