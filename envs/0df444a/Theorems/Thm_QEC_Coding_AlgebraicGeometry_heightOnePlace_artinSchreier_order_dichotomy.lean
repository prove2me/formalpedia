-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_artinSchreier_order_dichotomy
-- name    : QEC.Coding.AlgebraicGeometry.heightOnePlace_artinSchreier_order_dichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:31:38.700961+00:00
-- url     : https://prove2.me/theorems/f6422f6f-8eb8-4a9c-ab89-d121c53f3c15
-- title:
--   Algebraic Geometry: height One Place artin Schreier order dichotomy
-- statement:
--   The degree-two specialization of normalized root-order propagation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/HeightOneOrder.lean#L164-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/HeightOneOrder.lean#L164-L183

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.heightOnePlace_artinSchreier_order_dichotomy
    {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra k K] [Algebra k L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra R S] [FaithfulSMul R S] [Module.Finite R S]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    (H : IsDedekindDomain.HeightOneSpectrum R)
    (J : IsDedekindDomain.HeightOneSpectrum S) [J.asIdeal.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2)
    (ha : (heightOnePlace (k := k) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := k) (K := K) H).order a) :
    (heightOnePlace (k := k) (K := L) J).order y = -1 ∨
      0 ≤ (heightOnePlace (k := k) (K := L) J).order y := by sorry
