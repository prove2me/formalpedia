-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DiscreteAnalyticOrder_exists_uniformizer_order
-- name    : QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.exists_uniformizer_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:04:29.131559+00:00
-- url     : https://prove2.me/theorems/30c91f66-6749-457e-8229-c8750771549e
-- title:
--   Discrete Analytic Order: exists uniformizer order
-- statement:
--   A genuine DVR uniformizer has finite positive integer analytic order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean#L28-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/DiscreteAnalyticOrder.lean#L28-L38

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_DiscreteAnalyticOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
local notation "V" => Valuation.valuationSubring (AddValuation.toValuation v)

theorem QEC.Coding.AlgebraicGeometry.DiscreteAnalyticOrder.exists_uniformizer_order [IsDiscreteValuationRing V] :
    ∃ (π : V) (m : ℤ), Irreducible π ∧ 0 < m ∧ v (π : K) = (m : WithTop ℤ) := by sorry
