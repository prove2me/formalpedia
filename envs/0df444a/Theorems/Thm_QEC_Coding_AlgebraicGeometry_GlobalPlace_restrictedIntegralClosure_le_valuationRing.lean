-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_restrictedIntegralClosure_le_valuationRing
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.restrictedIntegralClosure_le_valuationRing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:18:53.40342+00:00
-- url     : https://prove2.me/theorems/03c4ebfe-504b-456b-b87f-8b6bab4e5173
-- title:
--   Global Place: restricted Integral Closure le valuation Ring
-- statement:
--   The literal integral closure of the restricted valuation ring lies in
--   the original ambient valuation ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RestrictedIntegralModel.lean#L31-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RestrictedIntegralModel.lean#L31-L43

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralModelCentre
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RestrictedIntegralModel
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GlobalPlace
noncomputable section
variable {k F E : Type*} [Field k] [Finite k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E] [Algebra.IsAlgebraic F E]
    (Q : GlobalPlace k E)
local notation "P" => Q.restrict (F := F)
local notation "A" => GlobalPlace.valuationRing (GlobalPlace.restrict (F := F) Q)
local notation "C" => integralClosure A E
variable [Algebra (Q.restrict (F := F)).valuationRing E]
    [IsScalarTower (Q.restrict (F := F)).valuationRing F E]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.restrictedIntegralClosure_le_valuationRing :
    (C).toSubring ≤ Q.valuationRing.toSubring := by sorry
