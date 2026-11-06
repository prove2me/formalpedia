-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_germDerivative_order
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.germDerivative_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:05:23.463433+00:00
-- url     : https://prove2.me/theorems/467e53ea-628c-4dc7-970d-b81ca8386bee
-- title:
--   Meromorphic Germs: germ Derivative order
-- statement:
--   A nonzero finite integer order decreases by one under actual complex differentiation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGermDifferentiation.lean#L107-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGermDifferentiation.lean#L107-L115

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGermDifferentiation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.germDerivative_order (x : ℂ) (A : MeromorphicGermRing x) (m : ℤ)
    (hm : m ≠ 0) (hA : meromorphicOrderValuation x A = (m : WithTop ℤ)) :
    meromorphicOrderValuation x (germDerivative x A) = ((m-1 : ℤ) : WithTop ℤ) := by sorry
