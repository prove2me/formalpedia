-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_order_eq_of_map_eq
-- name    : QEC.Coding.AlgebraicGeometry.heightOnePlace_order_eq_of_map_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:36:19.421566+00:00
-- url     : https://prove2.me/theorems/091e8990-266c-4ec6-b339-398062527967
-- title:
--   Algebraic Geometry: height One Place order eq of map eq
-- statement:
--   If a height-one prime maps to the supplied height-one prime of an
--   overring in the same fraction field, the normalized orders agree exactly.
--   The ramification index is derived to be one from the prime image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/HeightOneOrderTransport.lean#L97-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/HeightOneOrderTransport.lean#L97-L121

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.heightOnePlace_order_eq_of_map_eq
    {k R S L : Type*} [Field k] [Finite k]
    [CommRing R] [CommRing S] [Field L]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra k L] [Algebra R L] [Algebra S L]
    [IsFractionRing R L] [IsFractionRing S L]
    [Algebra R S] [FaithfulSMul R S] [IsScalarTower R S L]
    (H : IsDedekindDomain.HeightOneSpectrum R)
    (J : IsDedekindDomain.HeightOneSpectrum S) [J.asIdeal.LiesOver H.asIdeal]
    (hmap : Ideal.map (algebraMap R S) H.asIdeal = J.asIdeal) (x : L) :
    (heightOnePlace (k := k) (K := L) H).order x =
      (heightOnePlace (k := k) (K := L) J).order x := by sorry
