-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_order_eq_of_common_extension
-- name    : QEC.Coding.AlgebraicGeometry.heightOnePlace_order_eq_of_common_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:52:55.765975+00:00
-- url     : https://prove2.me/theorems/0e6514db-cf3c-4b4e-b255-7ef0f936892c
-- title:
--   Algebraic Geometry: height One Place order eq of common extension
-- statement:
--   Equality of the actual upper orders determines both normalized lower
--   orders. Their compatibility with restriction is computed from prime
--   multiplicities, not assumed for the lower places.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/HeightOneOrderTransport.lean#L54-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/HeightOneOrderTransport.lean#L54-L92

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.heightOnePlace_order_eq_of_common_extension
    {k R R' S S' K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [IsDedekindDomain R] [IsDedekindDomain R']
    [IsDedekindDomain S] [IsDedekindDomain S']
    [Algebra k K] [Algebra k L] [Algebra K L]
    [Algebra R K] [IsFractionRing R K] [Algebra R' K] [IsFractionRing R' K]
    [Algebra S L] [IsFractionRing S L] [Algebra S' L] [IsFractionRing S' L]
    [Algebra R S] [FaithfulSMul R S] [Module.Finite R S]
    [Algebra R' S'] [FaithfulSMul R' S'] [Module.Finite R' S']
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
    [Algebra R' L] [IsScalarTower R' K L] [IsScalarTower R' S' L]
    (P : IsDedekindDomain.HeightOneSpectrum R)
    (P' : IsDedekindDomain.HeightOneSpectrum R')
    (Q : IsDedekindDomain.HeightOneSpectrum S)
    (Q' : IsDedekindDomain.HeightOneSpectrum S')
    [Q.asIdeal.LiesOver P.asIdeal] [Q'.asIdeal.LiesOver P'.asIdeal]
    (hupper : (heightOnePlace (k := k) (K := L) Q).order =
      (heightOnePlace (k := k) (K := L) Q').order) :
    (heightOnePlace (k := k) (K := K) P).order =
      (heightOnePlace (k := k) (K := K) P').order := by sorry
