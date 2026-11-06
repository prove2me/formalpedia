-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_germDerivative_nonnegative
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.germDerivative_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:05:08.380554+00:00
-- url     : https://prove2.me/theorems/b46a4019-8adf-4be7-9bcb-56559d3b664a
-- title:
--   Meromorphic Germs: germ Derivative nonnegative
-- statement:
--   Differentiating a germ with an analytic representative preserves nonnegative order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGermDifferentiation.lean#L99-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGermDifferentiation.lean#L99-L104

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGermDifferentiation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.germDerivative_nonnegative (x : ℂ) (A : MeromorphicGermRing x)
    (hA : 0 ≤ meromorphicOrderValuation x A) :
    0 ≤ meromorphicOrderValuation x (germDerivative x A) := by sorry
