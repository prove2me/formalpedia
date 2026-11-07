-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_primePower_dvd_of_localized_dvd
-- name    : QEC.Coding.AlgebraicGeometry.primePower_dvd_of_localized_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:26:40.751885+00:00
-- url     : https://prove2.me/theorems/ae71848e-20c0-4081-b429-c6481a362bc4
-- title:
--   Algebraic Geometry: prime Power dvd of localized dvd
-- statement:
--   The Algebraic Geometry construction uses the prime Power dvd of localized dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFiberDescent.lean#L25-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFiberDescent.lean#L25-L46

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.Prime.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFiberDescent
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.primePower_dvd_of_localized_dvd
    {R : Type*} [CommRing R] [IsDomain R]
    (P : Ideal R) [P.IsPrime] (a : R) (hP : P = Ideal.span {a}) (ha : Prime a)
    (n : ℕ) (r : R)
    (h : (algebraMap R (Localization.AtPrime P) a)^n ∣
      algebraMap R (Localization.AtPrime P) r) : a^n ∣ r := by sorry
