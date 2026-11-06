-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOnePlace_order_integral
-- name    : QEC.Coding.AlgebraicGeometry.heightOnePlace_order_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:12:24.137703+00:00
-- url     : https://prove2.me/theorems/e64cb4d4-d04f-41b6-8ead-a2f1fe98b19d
-- title:
--   Algebraic Geometry: height One Place order integral
-- statement:
--   The Algebraic Geometry construction uses the height One Place order integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/HeightOneOrder.lean#L38-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/HeightOneOrder.lean#L38-L47

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ArtinSchreierOrder
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.heightOnePlace_order_integral
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra k K] [Algebra R K] [IsFractionRing R K]
    (H : IsDedekindDomain.HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    (heightOnePlace (k := k) (K := K) H).order (algebraMap R K r) =
      (multiplicity H.asIdeal (Ideal.span {r}) : ℤ) := by sorry
