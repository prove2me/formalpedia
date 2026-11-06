-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_order_algebraMap
-- name    : QEC.Coding.AlgebraicGeometry.heightOnePlace_order_algebraMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:12:20.945993+00:00
-- url     : https://prove2.me/theorems/66a136bd-ffa5-4409-b604-e592259a597d
-- title:
--   Algebraic Geometry: height One Place order algebra Map
-- statement:
--   At a fixed chain of global primes, restriction scales normalized orders
--   by the actual ramification index. No order compatibility is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/HeightOneOrder.lean#L77-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/HeightOneOrder.lean#L77-L126

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.heightOnePlace_order_algebraMap
    {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra k K] [Algebra k L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra R S] [FaithfulSMul R S] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    (H : IsDedekindDomain.HeightOneSpectrum R)
    (J : IsDedekindDomain.HeightOneSpectrum S) [J.asIdeal.LiesOver H.asIdeal]
    (x : K) (hx : x ≠ 0) :
    (heightOnePlace (k := k) (K := L) J).order (algebraMap K L x) =
      (H.asIdeal.ramificationIdx' J.asIdeal : ℤ) *
        (heightOnePlace (k := k) (K := K) H).order x := by sorry
