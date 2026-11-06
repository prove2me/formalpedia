-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_valuationRing
-- name    : QEC.Coding.AlgebraicGeometry.heightOnePlace_valuationRing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:36:00.406391+00:00
-- url     : https://prove2.me/theorems/20edefd3-39cc-435f-ac86-bf5c6fde10a8
-- title:
--   Algebraic Geometry: height One Place valuation Ring
-- statement:
--   The prime's normalized place has precisely its canonical localization
--   as valuation ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/HeightOneOrder.lean#L31-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/HeightOneOrder.lean#L31-L36

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.heightOnePlace_valuationRing
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra k K] [Algebra R K] [IsFractionRing R K]
    (H : IsDedekindDomain.HeightOneSpectrum R) :
    H.valuationSubringAtPrime K = (heightOnePlace (k := k) (K := K) H).valuationRing := by sorry
