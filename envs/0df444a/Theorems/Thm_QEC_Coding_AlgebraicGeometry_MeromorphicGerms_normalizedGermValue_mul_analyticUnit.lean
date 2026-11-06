-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_normalizedGermValue_mul_analyticUnit
-- name    : QEC.Coding.AlgebraicGeometry.MeromorphicGerms.normalizedGermValue_mul_analyticUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:57:07.179949+00:00
-- url     : https://prove2.me/theorems/f90304b8-b665-4cc3-b632-851f8d1b4d96
-- title:
--   Meromorphic Germs: normalized Germ Value mul analytic Unit
-- statement:
--   Normal-form value commutes with multiplication by a genuine analytic unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/NormalizedGermUnits.lean#L15-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/NormalizedGermUnits.lean#L15-L26

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedGermUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
open scoped Manifold ContDiff
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.MeromorphicGerms.normalizedGermValue_mul_analyticUnit
    (f u : ℂ → ℂ) (x : ℂ) (hf : MeromorphicAt f x)
    (hu : AnalyticAt ℂ u x) (hunit : u x ≠ 0) :
    toMeromorphicNFAt (f * u) x x = toMeromorphicNFAt f x x * u x := by sorry
