-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehler_field_map_zero_heightOne_clear
-- name    : QEC.Coding.AlgebraicGeometry.kaehler_field_map_zero_heightOne_clear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:10:36.73946+00:00
-- url     : https://prove2.me/theorems/3d1518b8-b1fb-4644-9837-0721e9d22065
-- title:
--   Algebraic Geometry: kaehler field map zero height One clear
-- statement:
--   A proved local differential injection clears an affine kernel element by a scalar outside its actual height-one centre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineKaehlerInjective.lean#L58-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineKaehlerInjective.lean#L58-L90

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.Algebra.GroupWithZero.Action.Units
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
variable [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable [SMulCommClass R A K] [IsDedekindDomain A] [IsFractionRing A K]
variable (H : IsDedekindDomain.HeightOneSpectrum A) (T : ValuationSubring K)
variable [Algebra R T] [Algebra T K] [IsScalarTower R T K] [SMulCommClass R T K]

theorem QEC.Coding.AlgebraicGeometry.kaehler_field_map_zero_heightOne_clear
    (heq : H.valuationSubringAtPrime K = T)
    (hT : ∀ t : T, algebraMap T K t = t.val)
    (hTin : Function.Injective (KaehlerDifferential.map R R T K))
    (tau : KaehlerDifferential R A)
    (hzero : KaehlerDifferential.map R R A K tau = 0) :
    ∃ s : A, s ∉ H.asIdeal ∧ s • tau = 0 := by sorry
