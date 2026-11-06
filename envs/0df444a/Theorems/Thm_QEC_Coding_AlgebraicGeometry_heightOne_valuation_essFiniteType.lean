-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOne_valuation_essFiniteType
-- name    : QEC.Coding.AlgebraicGeometry.heightOne_valuation_essFiniteType
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:10:22.518287+00:00
-- url     : https://prove2.me/theorems/9316141d-e1ce-40e2-8b53-e32eb443c2ea
-- title:
--   Algebraic Geometry: height One valuation ess Finite Type
-- statement:
--   Transport actual height-one localization and compatible literal scalar maps to derive essential finite type of the same-field valuation ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineKaehlerInjective.lean#L25-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineKaehlerInjective.lean#L25-L43

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.Algebra.GroupWithZero.Action.Units
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
variable [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable [IsDedekindDomain A] [IsFractionRing A K] [Algebra.EssFiniteType R A]
variable (H : IsDedekindDomain.HeightOneSpectrum A) (T : ValuationSubring K)
variable [Algebra R T] [Algebra T K] [IsScalarTower R T K]

theorem QEC.Coding.AlgebraicGeometry.heightOne_valuation_essFiniteType
    (heq : H.valuationSubringAtPrime K = T)
    (hT : ∀ t : T, algebraMap T K t = t.val) :
    Algebra.EssFiniteType R T := by sorry
