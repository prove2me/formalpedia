-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_exists_heightOne_order_eq
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.exists_heightOne_order_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:18:45.06347+00:00
-- url     : https://prove2.me/theorems/9541d2cd-801b-4e39-a952-fe9f4d2d9089
-- title:
--   Global Place: exists height One order eq
-- statement:
--   Construct the height-one centre of the supplied actual place on any
--   Dedekind fraction model contained in its valuation ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/IntegralModelCentre.lean#L19-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/IntegralModelCentre.lean#L19-L66

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralModelCentre
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.exists_heightOne_order_eq
    {k E : Type*} [Field k] [Finite k] [Field E] [Algebra k E]
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R E] [IsFractionRing R E] (Q : GlobalPlace k E)
    (hR : ∀ r : R, Q.valuation (algebraMap R E r) ≤ 1)
    (hn : ∃ r : R, r ≠ 0 ∧ Q.valuation (algebraMap R E r) < 1) :
    ∃ H : IsDedekindDomain.HeightOneSpectrum R,
      H.valuationSubringAtPrime E = Q.valuationRing ∧
        (heightOnePlace (k := k) (K := E) H).order = Q.order := by sorry
