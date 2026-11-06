-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_exists_splitUpperPrime_auxiliary_mem_of_evaluate_eq_zero
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_splitUpperPrime_auxiliary_mem_of_evaluate_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:56:49.063917+00:00
-- url     : https://prove2.me/theorems/8f08caf4-1dff-4d98-a6eb-f37fec76794d
-- title:
--   F256 Garcia Stichtenoth: exists split Upper Prime auxiliary mem of evaluate eq zero
-- statement:
--   If the base coordinate reduces to zero, one of the concrete split upper
--   primes contains the actual auxiliary coordinate.  This selects the unique
--   zero branch used by the common-zero path; it does not store a ramification or
--   divisor conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SplittingIdeals.lean#L126-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SplittingIdeals.lean#L126-L152

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitIntegralClosure
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplittingIdeals
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_splitUpperPrime_auxiliary_mem_of_evaluate_eq_zero
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hzero : Q.evaluateRegular x hregular = 0) :
    ∃ c : LinearMap.ker f256ArtinSchreier,
      splitIntegralAuxiliaryCoordinate Q P x hx hregular ∈
        (splitUpperPrime Q P x hx c).1 := by sorry
